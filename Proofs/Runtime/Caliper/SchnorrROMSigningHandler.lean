import Proofs.Runtime.Caliper.SchnorrROMSigningHandlerRoute

/-! Execute both shared-tape private draws, the signing arithmetic and the
managed-cache update. Context retained across either call is stored by charged
Caliper copies; the LIVE table and updated tapes are returned in source order. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G C : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G C) (zeroValid : layout.sampler.tape.scalar.valid 0)
    (scale : Implementation .unit layout.core.arithmetic.scaleArgs layout.core.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.core.arithmetic.points layout.core.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

def result (value : (PrivateSampler.Pair.output layout.sampler).Value × layout.context.Value) : layout.output.Value :=
  finishValue layout
    (⟨Core.value (coreValue layout value).1.val,
      (Core.implementation layout.core zeroValid scale sub scaleBuffers subBuffers reserve).preserves
        (coreValue layout value).1.val (coreValue layout value).1.property⟩, (coreValue layout value).2)

theorem coreNameFits :
    (Core.implementation layout.core zeroValid scale sub scaleBuffers subBuffers reserve).program.savedBuffer < 2 ^ w := by
  have bound := Core.buffers layout.core zeroValid scale sub scaleBuffers subBuffers reserve
  have := layout.sampler.tape.wordFits
  unfold Realizer.savedBuffer
  omega

def retainedCore := (Core.implementation layout.core zeroValid scale sub scaleBuffers subBuffers reserve).program.retain
  (by decide) layout.saved.representation layout.sampler.tape.wordFits
    (coreNameFits layout zeroValid scale sub scaleBuffers subBuffers reserve) layout.work.fits layout.finished.fits
def finish : Realizer .unit layout.sampled layout.output.representation
    (result layout zeroValid scale sub scaleBuffers subBuffers reserve) :=
  ((prepareCore layout).then (retainedCore layout zeroValid scale sub scaleBuffers subBuffers reserve)).viewOutput
    layout.output.representation (result layout zeroValid scale sub scaleBuffers subBuffers reserve)
    (fun _ => finish_bytes layout _)

variable (caller : PrivateSampler.Caller layout.sampler)

def retained (fuel : Nat) := Interactive.retain (PrivateSampler.Pair.code layout.sampler caller zeroValid fuel)
  (Interactive.savedBuffer (Fresh.port layout.sampler.tape) (PrivateSampler.Pair.code layout.sampler caller zeroValid fuel))
  (Read.tapes layout.sampler.tape).representation.encoding.words (PrivateSampler.Pair.output layout.sampler).representation.encoding.words
  layout.context.representation.encoding.words
def code (fuel : Nat) : Interactive.Code w := .seq (.compute (prepare layout).code)
  (.seq (retained layout zeroValid caller fuel) (.compute (finish layout zeroValid scale sub scaleBuffers subBuffers reserve).code))
def ready (fuel : Nat) (value : layout.input.Value) := PrivateSampler.Pair.ready layout.sampler fuel (tapes layout value)
def source (fuel : Nat) (value : layout.input.Value) : ProbComp layout.output.Value :=
  (fun sampled => result layout zeroValid scale sub scaleBuffers subBuffers reserve (sampled, context layout value)) <$>
    PrivateSampler.Pair.source layout.sampler caller zeroValid fuel (tapes layout value)

omit [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G] in
theorem retained_refines (fuel : Nat) :
    Interactive.RefinesOn (fun value => PrivateSampler.Pair.ready layout.sampler fuel value.1) (Fresh.port layout.sampler.tape) .unit
      layout.prepared layout.sampled
      (fun value => (fun answer => (answer, value.2)) <$> PrivateSampler.Pair.source layout.sampler caller zeroValid fuel value.1)
      (retained layout zeroValid caller fuel) :=
  (PrivateSampler.Pair.refines layout.sampler caller zeroValid fuel).retain (by decide) layout.context.representation
    layout.sampler.tape.wordFits layout.prepared.fits layout.sampled.fits

theorem refines (fuel : Nat) : Interactive.RefinesOn (ready layout fuel) (Fresh.port layout.sampler.tape) .unit
    layout.input.representation layout.output.representation
    (source layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel)
    (code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel) := by
  have suffix := (retained_refines layout zeroValid caller fuel).seq
    ((Interactive.Refines.compute (Fresh.port layout.sampler.tape) .unit
      (finish layout zeroValid scale sub scaleBuffers subBuffers reserve)).on (fun _ => True)) (by intros; trivial)
  have combined := ((Interactive.Refines.compute (Fresh.port layout.sampler.tape) .unit (prepare layout)).on
    (ready layout fuel)).seq suffix (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  convert combined using 1
  · funext value
    simp only [source, pure_bind, bind_pure_comp, Functor.map_map]
    rfl
  · rfl

theorem preserves_live (fuel : Nat) (value : layout.input.Value) (answer : layout.output.Value)
    (reached : answer ∈ support (source layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel value)) :
    answer.val.2.1.2.2 = value.val.2.1.2.2 := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨sampled, _, rfl⟩ := reached
  rfl

theorem managed_length (fuel : Nat) (value : layout.input.Value) (answer : layout.output.Value)
    (reached : answer ∈ support (source layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel value)) :
    answer.val.2.1.2.1.length ≤ value.val.2.1.2.1.length + 1 := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨sampled, _, rfl⟩ := reached
  exact Core.length _

theorem reserved_after (fuel remaining : Nat) (value : layout.input.Value)
    (room : PrivateHandler.Reserved layout.sampler.tape (fuel + fuel + remaining) (tapes layout value))
    (answer : layout.output.Value)
    (reached : answer ∈ support (source layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel value)) :
    answer.val.2.2.1.length + remaining ≤ layout.sampler.tape.capacity := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨sampled, supported, rfl⟩ := reached
  exact PrivateSampler.Pair.reserved_after layout.sampler caller zeroValid fuel remaining (tapes layout value) room sampled supported

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
