import Signatures.Runtime.Caliper.SchnorrROMSigningHandlerSource

/-! Signing wrapper costs include sampling, local group routines, cache access
and every retained or routed word. They depend on bounded frame widths and
local caller contracts, without assuming a completed signing implementation. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
open Caliper BoundedSource SchnorrROMTape OracleComp OracleSpec
variable {w : Nat} {M F G C : Type} [Zero F] [SMul F G] [Sub G] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G C) (zeroValid : layout.sampler.tape.scalar.valid 0)
    (scale : Implementation .unit layout.core.arithmetic.scaleArgs layout.core.point (fun value => value.1 • value.2))
    (sub : Implementation .unit layout.core.arithmetic.points layout.core.point (fun value => value.1 - value.2))
    {slots : Nat} (scaleBuffers : scale.program.code.memBound ≤ slots) (subBuffers : sub.program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w)

def finishTime (scaleTime subTime : Nat) := Core.timeBudget layout.core scaleTime subTime +
  8 * layout.work.encoding.words + 8 * layout.core.input.representation.encoding.words +
  8 * layout.core.output.representation.encoding.words + 12 * layout.saved.representation.encoding.words
def finishWords (scaleWords subWords : Nat) := Core.codeBudget layout.core scaleWords subWords +
  26 * layout.work.encoding.words + 26 * layout.core.input.representation.encoding.words +
  26 * layout.core.output.representation.encoding.words + 39 * layout.saved.representation.encoding.words + 54

theorem finish_time {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords)
    (value : (PrivateSampler.Pair.output layout.sampler).Value × layout.context.Value) :
    (finish layout zeroValid scale sub scaleBuffers subBuffers reserve).time value ≤ finishTime layout scaleTime subTime := by
  have computed := (Core.bounded layout.core zeroValid scale sub scaleBuffers subBuffers reserve scaleBound subBound).time_le
    (coreValue layout value).1
  have routed := core_time layout value
  have copied := (Core.implementation layout.core zeroValid scale sub scaleBuffers subBuffers reserve).program.retain_time_unit_le
    layout.saved.representation layout.sampler.tape.wordFits (coreNameFits layout zeroValid scale sub scaleBuffers subBuffers reserve)
    layout.work.fits layout.finished.fits (coreValue layout value)
  change (retainedCore layout zeroValid scale sub scaleBuffers subBuffers reserve).time (coreValue layout value) ≤ _ at copied
  change (prepareCore layout).time value + (retainedCore layout zeroValid scale sub scaleBuffers subBuffers reserve).time (coreValue layout value) ≤ _
  unfold finishTime
  omega

theorem finish_words {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords) :
    descriptionWords (finish layout zeroValid scale sub scaleBuffers subBuffers reserve).code ≤ finishWords layout scaleWords subWords := by
  have computed := (Core.bounded layout.core zeroValid scale sub scaleBuffers subBuffers reserve scaleBound subBound).code_le
  have routed := core_words layout
  have copied := (Core.implementation layout.core zeroValid scale sub scaleBuffers subBuffers reserve).program.retain_descriptionWords_le
    (by decide) layout.saved.representation layout.sampler.tape.wordFits (coreNameFits layout zeroValid scale sub scaleBuffers subBuffers reserve)
    layout.work.fits layout.finished.fits
  change descriptionWords (retainedCore layout zeroValid scale sub scaleBuffers subBuffers reserve).code ≤ _ at copied
  change descriptionWords ((prepareCore layout).code ;; (retainedCore layout zeroValid scale sub scaleBuffers subBuffers reserve).code) ≤ _
  rw [descriptionWords_seq]
  unfold finishWords
  omega

theorem finish_buffers : (finish layout zeroValid scale sub scaleBuffers subBuffers reserve).code.memBound ≤ max 10 (slots + 3) := by
  have computed := Core.buffers layout.core zeroValid scale sub scaleBuffers subBuffers reserve
  have copied := (Core.implementation layout.core zeroValid scale sub scaleBuffers subBuffers reserve).program.retain_buffers
    (by decide) layout.saved.representation layout.sampler.tape.wordFits (coreNameFits layout zeroValid scale sub scaleBuffers subBuffers reserve)
    layout.work.fits layout.finished.fits
  have routed := core_buffers layout
  change (retainedCore layout zeroValid scale sub scaleBuffers subBuffers reserve).code.memBound ≤ _ at copied
  change max (prepareCore layout).code.memBound (retainedCore layout zeroValid scale sub scaleBuffers subBuffers reserve).code.memBound ≤ _
  omega

theorem finish_names (names : Nat) (scaleNames : NamesAccounted scale.program.code names) (subNames : NamesAccounted sub.program.code names) :
    NamesAccounted (finish layout zeroValid scale sub scaleBuffers subBuffers reserve).code (max 5 names) :=
  (core_names layout _).seq (Retain.names
    (Core.names layout.core zeroValid scale sub scaleBuffers subBuffers reserve names scaleNames subNames) _ _ _)

variable (caller : PrivateSampler.Caller layout.sampler)

def timeBudget (localTime initialTime fuel scaleTime subTime : Nat) :=
  PrivateSampler.Pair.timeBudget layout.sampler zeroValid localTime initialTime fuel +
  8 * layout.prepared.encoding.words + 8 * (Read.tapes layout.sampler.tape).representation.encoding.words +
  8 * (PrivateSampler.Pair.output layout.sampler).representation.encoding.words + 12 * layout.context.representation.encoding.words +
  finishTime layout scaleTime subTime
def codeBudget (fuel scaleWords subWords : Nat) := PrivateSampler.Pair.codeBudget layout.sampler caller zeroValid fuel +
  26 * layout.prepared.encoding.words + 26 * (Read.tapes layout.sampler.tape).representation.encoding.words +
  26 * (PrivateSampler.Pair.output layout.sampler).representation.encoding.words + 39 * layout.context.representation.encoding.words +
  finishWords layout scaleWords subWords + 59
def nameBudget (localNames primitiveNames : Nat) := max (PrivateSampler.nameBudget layout.sampler zeroValid localNames) (max 5 primitiveNames)

theorem time_bound (fuel localTime initialTime : Nat)
    (localBound : ∀ value, caller.continuation.time value ≤ localTime) (initialBound : ∀ value, caller.initialCode.time value ≤ initialTime)
    {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords) :
    Interactive.TimeBoundOn (ready layout fuel) (Fresh.port layout.sampler.tape) .unit layout.input.representation
      (code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel) (timeBudget layout zeroValid localTime initialTime fuel scaleTime subTime) := by
  have held := (Interactive.TimeBoundOn.retain (PrivateSampler.Pair.refines layout.sampler caller zeroValid fuel)
    (PrivateSampler.Pair.time_bound layout.sampler caller zeroValid fuel localTime initialTime localBound initialBound)
    (by decide) layout.context.representation layout.sampler.tape.wordFits layout.prepared.fits).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
  have finished := (Interactive.TimeBound.compute (port := Fresh.port layout.sampler.tape) (cost := .unit)
    (finish layout zeroValid scale sub scaleBuffers subBuffers reserve) (finishTime layout scaleTime subTime)
    (finish_time layout zeroValid scale sub scaleBuffers subBuffers reserve scaleBound subBound)).on (fun _ => True)
  have suffix := Interactive.TimeBoundOn.seq (retained_refines layout zeroValid caller fuel) held finished (by intros; trivial)
  have prepared := (Interactive.TimeBound.compute (port := Fresh.port layout.sampler.tape) (cost := .unit)
    (prepare layout) (8 * layout.prepared.encoding.words) (prepare_time layout)).on (ready layout fuel)
  have combined := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute (Fresh.port layout.sampler.tape) .unit (prepare layout)).on (ready layout fuel))
    prepared suffix (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  exact combined.mono (by unfold timeBudget; omega)

theorem code_bound (fuel : Nat) {scaleTime subTime scaleWords subWords : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (subBound : sub.BoundedBy subTime subWords) :
    ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape)).descriptionWords ≤
      codeBudget layout zeroValid caller fuel scaleWords subWords := by
  have sampled := PrivateSampler.Pair.code_bound layout.sampler caller zeroValid fuel
  have prepared := prepare_words layout
  have finished := finish_words layout zeroValid scale sub scaleBuffers subBuffers reserve scaleBound subBound
  have held := Interactive.retain_descriptionWords_le (Fresh.port layout.sampler.tape)
    (PrivateSampler.Pair.code layout.sampler caller zeroValid fuel)
    (Interactive.savedBuffer (Fresh.port layout.sampler.tape) (PrivateSampler.Pair.code layout.sampler caller zeroValid fuel))
    (Read.tapes layout.sampler.tape).representation.encoding.words (PrivateSampler.Pair.output layout.sampler).representation.encoding.words
    layout.context.representation.encoding.words
  change ((retained layout zeroValid caller fuel).lower (Fresh.port layout.sampler.tape)).descriptionWords ≤ _ at held
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem names (fuel localNames primitiveNames : Nat)
    (localBound : NamesAccounted caller.continuation.code localNames) (initialBound : NamesAccounted caller.initialCode.code localNames)
    (scaleNames : NamesAccounted scale.program.code primitiveNames) (subNames : NamesAccounted sub.program.code primitiveNames) :
    WordIO.NamesAccounted ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape))
      (nameBudget layout zeroValid localNames primitiveNames) := by
  have held := Interactive.retain_names (Fresh.port layout.sampler.tape)
    (PrivateSampler.Pair.names layout.sampler caller zeroValid fuel localNames localBound initialBound)
    (Read.tapes layout.sampler.tape).representation.encoding.words (PrivateSampler.Pair.output layout.sampler).representation.encoding.words
    layout.context.representation.encoding.words
  exact (WordIO.NamesAccounted.compute (prepare_names layout _)).seq
    ((held.mono (Nat.le_max_left _ _)).seq (WordIO.NamesAccounted.compute
      ((finish_names layout zeroValid scale sub scaleBuffers subBuffers reserve primitiveNames scaleNames subNames).mono (Nat.le_max_right _ _))))

theorem buffers (fuel : Nat) :
    ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape)).memBound ≤
      max (PrivateSampler.Service.bufferBudget layout.sampler caller + 2) (max 10 (slots + 3)) := by
  have prepared := prepare_buffers layout
  have sampled := PrivateSampler.Pair.buffers layout.sampler caller zeroValid fuel
  have held := Interactive.retain_buffers (Fresh.port layout.sampler.tape) (PrivateSampler.Pair.code layout.sampler caller zeroValid fuel)
    (Read.tapes layout.sampler.tape).representation.encoding.words (PrivateSampler.Pair.output layout.sampler).representation.encoding.words
    layout.context.representation.encoding.words
  have finished := finish_buffers layout zeroValid scale sub scaleBuffers subBuffers reserve
  change ((retained layout zeroValid caller fuel).lower (Fresh.port layout.sampler.tape)).memBound ≤ _ at held
  change max (prepare layout).code.memBound
    (max ((retained layout zeroValid caller fuel).lower (Fresh.port layout.sampler.tape)).memBound
      (finish layout zeroValid scale sub scaleBuffers subBuffers reserve).code.memBound) ≤ _
  unfold PrivateSampler.Service.bufferBudget at *
  omega

theorem descriptionFits (fuel : Nat)
    (localHeadroom : caller.continuation.code.memBound + 2 < 2 ^ w)
    (initialHeadroom : caller.initialCode.code.memBound + 2 < 2 ^ w) :
    ((code layout zeroValid scale sub scaleBuffers subBuffers reserve caller fuel).lower (Fresh.port layout.sampler.tape)).DescriptionFits := by
  have pairFits := PrivateSampler.Pair.descriptionFits layout.sampler caller zeroValid fuel (by omega) (by omega)
  have savedFits : Interactive.savedBuffer (Fresh.port layout.sampler.tape) (PrivateSampler.Pair.code layout.sampler caller zeroValid fuel) < 2 ^ w := by
    have bound := PrivateSampler.Pair.buffers layout.sampler caller zeroValid fuel
    have := layout.sampler.tape.wordFits
    unfold Interactive.savedBuffer
    unfold PrivateSampler.Service.bufferBudget at bound
    omega
  have held := Interactive.retain_descriptionFits (Fresh.port layout.sampler.tape)
    (PrivateSampler.Pair.code layout.sampler caller zeroValid fuel) _ _ _ _ layout.sampler.tape.wordFits pairFits savedFits
    (Read.tapes layout.sampler.tape).representation.fits layout.context.representation.fits layout.sampled.fits
  exact .seq layout.sampler.tape.wordFits (.compute (prepare layout).description_fits)
    (.seq layout.sampler.tape.wordFits held (.compute (finish layout zeroValid scale sub scaleBuffers subBuffers reserve).description_fits))

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Handler
