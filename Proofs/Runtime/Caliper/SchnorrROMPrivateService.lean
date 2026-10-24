import Proofs.Runtime.Caliper.SchnorrROMPrivateFinish
import Proofs.Runtime.Caliper.InteractiveInvariantViews
import Proofs.Runtime.Caliper.CallerPostcondition

/-! A usable private scalar-sampling service. Its input is the shared pair of
tapes and its output is the scalar and updated tapes. Initialization, replay,
caller resumption and removal of the returned control packet all execute code. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Service
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F C : Type} [Zero F] (layout : Layouts w F C)
    (caller : Caller layout) (zeroValid : layout.tape.scalar.valid 0)

def unit : layout.tape.unit.Value := ⟨(), trivial⟩
def ready (fuel : Nat) (saved : Store layout) := PrivateHandler.Reserved layout.tape fuel saved
def code (fuel : Nat) : Interactive.Code w :=
  .seq (PrivateSampler.code layout caller zeroValid fuel) (.compute (Finish.program layout ⟨0, zeroValid⟩).code)
def pack (value : layout.tape.scalar.Value × Store layout) : (Reply.scalarOutput layout.tape).Value :=
  ⟨(value.1.val, value.2.val), value.1.property, value.2.property⟩
def source (fuel : Nat) (saved : Store layout) : ProbComp (Reply.scalarOutput layout.tape).Value :=
  (fun packet => pack layout (Finish.value layout ⟨0, zeroValid⟩ packet)) <$>
    PrivateSampler.source layout caller zeroValid fuel (unit layout, saved)

theorem refines (fuel : Nat) : Interactive.RefinesOn (ready layout fuel) (Fresh.port layout.tape) .unit
    (Read.tapes layout.tape).representation (Reply.scalarOutput layout.tape).representation
    (source layout caller zeroValid fuel) (code layout caller zeroValid fuel) := by
  have converted := (PrivateSampler.refines layout caller zeroValid fuel).seq
    ((Interactive.Refines.compute (Fresh.port layout.tape) .unit (Finish.program layout ⟨0, zeroValid⟩)).on (fun _ => True))
    (by intros; trivial)
  have inputView := converted.viewInput (Read.tapes layout.tape).representation (fun saved => (unit layout, saved)) (fun _ => rfl)
  have outputView := inputView.viewOutput (Reply.scalarOutput layout.tape).representation
    (pack layout) (fun _ => rfl)
  convert outputView using 1
  · rfl
  · funext saved
    simp only [source, bind_pure_comp, Functor.map_map]
  · rfl

theorem controller_source (fuel : Nat) (terminates : Terminates layout caller fuel)
    (saved : Store layout) (valid : ready layout fuel saved) :
    CallerMachine.observe (PrivateHandler.stored layout.tape) <$>
      PrivateSampler.source layout caller zeroValid fuel (unit layout, saved) =
        (fun result => (some result.1, result.2)) <$>
          (simulateQ Schnorr.RawTape.Private.oracle (original layout caller fuel terminates (unit layout))).run
            (PrivateHandler.stored layout.tape saved) := by
  let value := (unit layout, saved)
  let before := (PrivateSampler.input layout).initial value
  have holds := (PrivateSampler.input layout).initial_holds value
  have refined := (PrivateSampler.refines layout caller zeroValid fuel).observe RandomTape.zero value valid before holds
  have original := PrivateSampler.observe_source layout caller zeroValid fuel terminates RandomTape.zero value valid before holds
  have mapped := congrArg (Functor.map (Option.map (CallerMachine.observe (PrivateHandler.stored layout.tape)))) refined
  simp only [Functor.map_map, Option.map_some] at mapped
  apply (map_inj_right (fun h => Option.some.inj h)).mp
  simpa only [Functor.map_map] using mapped.symm.trans original

def completed (value : Option layout.tape.scalar.Value × Schnorr.RawTape.State F) :=
  ((value.1.getD ⟨0, zeroValid⟩).val, value.2.saved, value.2.remaining)

theorem source_original (fuel : Nat) (terminates : Terminates layout caller fuel)
    (saved : Store layout) (valid : ready layout fuel saved) :
    Subtype.val <$> source layout caller zeroValid fuel saved =
      (fun result => (result.1.val, result.2.saved, result.2.remaining)) <$>
        (simulateQ Schnorr.RawTape.Private.oracle (original layout caller fuel terminates (unit layout))).run
          (PrivateHandler.stored layout.tape saved) := by
  have mapped := congrArg (Functor.map (completed layout zeroValid)) (controller_source layout caller zeroValid fuel terminates saved valid)
  simp only [Functor.map_map] at mapped
  have same : (fun packet => (pack layout (Finish.value layout ⟨0, zeroValid⟩ packet)).val) =
      (fun packet => completed layout zeroValid (CallerMachine.observe (PrivateHandler.stored layout.tape) packet)) := by
    funext packet
    rcases packet with ⟨result | pending, saved⟩ <;> rfl
  unfold source
  rw [Functor.map_map]
  rw [same]
  simpa only [Function.comp_def, completed, Option.getD_some] using mapped

theorem scalar_source [SampleableType F] (fuel : Nat) (terminates : Terminates layout caller fuel)
    (samples : Subtype.val <$> original layout caller fuel terminates (unit layout) = ($ᵗ F : ProbComp F))
    (saved : Store layout) (valid : ready layout fuel saved) :
    Subtype.val <$> source layout caller zeroValid fuel saved =
      Caller.scalarResult <$> simulateQ _root_.Schnorr.LazyROM.sample
        ((simulateQ Schnorr.RawTape.oracle (Schnorr.privateImpl (.inr ()))).run (PrivateHandler.stored layout.tape saved)) := by
  rw [source_original layout caller zeroValid fuel terminates saved valid]
  have same := congrArg (Functor.map (Caller.scalarResult (F := F)))
    (PrivateSampler.scalar_source layout caller fuel terminates (unit layout) samples (PrivateHandler.stored layout.tape saved))
  simpa only [Functor.map_map, Caller.scalarResult] using same

theorem observe_scalar [SampleableType F] (fuel : Nat) (terminates : Terminates layout caller fuel)
    (samples : Subtype.val <$> original layout caller fuel terminates (unit layout) = ($ᵗ F : ProbComp F))
    (tape : RandomTape w) (saved : Store layout) (valid : ready layout fuel saved)
    (before : State w) (holds : (Read.tapes layout.tape).representation.Holds saved before) :
    (fun result => (Interactive.observe (Reply.scalarOutput layout.tape).representation result).map Subtype.val) <$>
      (code layout caller zeroValid fuel).execute (Fresh.port layout.tape) .unit tape before =
        some <$> (Caller.scalarResult <$> simulateQ _root_.Schnorr.LazyROM.sample
          ((simulateQ Schnorr.RawTape.oracle (Schnorr.privateImpl (.inr ()))).run (PrivateHandler.stored layout.tape saved))) := by
  have observed := (refines layout caller zeroValid fuel).observe tape saved valid before holds
  have mapped := congrArg (Functor.map (Option.map Subtype.val)) observed
  simp only [Functor.map_map, Option.map_some] at mapped
  have same := scalar_source layout caller zeroValid fuel terminates samples saved valid
  simpa only [Functor.map_map, Option.map_some] using mapped.trans (by
    simpa only [Functor.map_map] using congrArg (Functor.map some) same)

/-- Sampling leaves any additional reserved slots available to subsequent
sampling or signing. This postcondition also holds at an early return/cutoff. -/
theorem reserved_after (fuel reserve : Nat) (saved : Store layout)
    (room : PrivateHandler.Reserved layout.tape (fuel + reserve) saved)
    (answer : (Reply.scalarOutput layout.tape).Value)
    (reached : answer ∈ support (source layout caller zeroValid fuel saved)) :
    answer.val.2.1.length + reserve ≤ layout.tape.capacity := by
  simp only [source, support_map, Set.mem_image] at reached
  obtain ⟨packet, supported, rfl⟩ := reached
  have remaining := CallerControl.start_store caller.advance (PrivateHandler.source layout.tape zeroValid)
    (fun calls saved => PrivateHandler.Reserved layout.tape (calls + reserve) saved)
    (by intro small large saved less valid; unfold PrivateHandler.Reserved at *; omega)
    (by
      intro remaining q saved valid reply reached
      apply PrivateHandler.reserved_after layout.tape zeroValid (q, saved) (calls := remaining + reserve) _ reply reached
      change saved.val.1.length + (remaining + reserve + 1) ≤ layout.tape.capacity
      change saved.val.1.length + (remaining + 1 + reserve) ≤ layout.tape.capacity at valid
      omega)
    fuel (caller.initial (unit layout), saved) room packet supported
  change packet.2.val.1.length + reserve ≤ layout.tape.capacity
  simpa only [PrivateHandler.Reserved, Nat.zero_add] using remaining

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Service
