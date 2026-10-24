import Proofs.Runtime.Caliper.SchnorrROMPrivateSampler

/-! Complete resource bounds for the generated adaptive private sampler.
Only its local initialization and continuation have supplied resource bounds;
the replay handler and all suspension, copying and control costs are derived. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F C : Type} [Zero F] (layout : Layouts w F C)
    (caller : Caller layout) (zeroValid : layout.tape.scalar.valid 0)

def timeBudget (localTime initialTime fuel : Nat) :=
  CallerControl.timeBudget layout.tape.unit.representation.encoding.words (CallerStep.width (step layout))
    (PrivateQuery.timeBudget layout.tape zeroValid) localTime initialTime fuel
def codeBudget (fuel : Nat) := CallerControl.programWords (step layout) (Fresh.port layout.tape)
  caller.advance caller.continuation (PrivateQuery.code layout.tape zeroValid)
  layout.tape.unit.representation caller.initial caller.initialCode fuel
def nameBudget (slots : Nat) := max 3 (max slots (PrivateQuery.nameBudget layout.tape zeroValid))

theorem code_bound (fuel : Nat) :
    ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).descriptionWords ≤ codeBudget layout caller zeroValid fuel :=
  CallerControl.program_words (step layout) (Fresh.port layout.tape) caller.advance caller.continuation caller.localFits
    (PrivateQuery.code layout.tape zeroValid) layout.tape.unit.representation caller.initial caller.initialCode caller.initialFits
    (inputFits layout) fuel

theorem descriptionFits (fuel : Nat) :
    ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).DescriptionFits := by
  apply CallerControl.program_descriptionFits (step layout) (Fresh.port layout.tape) caller.advance caller.continuation caller.localFits
    (PrivateQuery.code layout.tape zeroValid) layout.tape.unit.representation caller.initial caller.initialCode caller.initialFits
    (inputFits layout) (PrivateQuery.descriptionFits layout.tape zeroValid) _ fuel
  have bounded := PrivateQuery.buffers layout.tape zeroValid
  have := layout.tape.wordFits
  dsimp only [Interactive.savedBuffer]
  omega

theorem time_bound (fuel localTime initialTime : Nat)
    (localBound : ∀ value, caller.continuation.time value ≤ localTime)
    (initialBound : ∀ value, caller.initialCode.time value ≤ initialTime) :
    Interactive.TimeBoundOn (admissible layout fuel) (Fresh.port layout.tape) .unit (input layout)
      (code layout caller zeroValid fuel) (timeBudget layout zeroValid localTime initialTime fuel) :=
  CallerControl.program_time (step layout) (Fresh.port layout.tape) caller.advance caller.continuation caller.localFits
    (invariant layout) (PrivateHandler.ready layout.tape) (PrivateHandler.refines layout.tape zeroValid)
    (fun _ value valid => PrivateHandler.ready_of_reserved layout.tape (value.1.1, value.2) valid)
    (PrivateHandler.time_bound layout.tape zeroValid) localBound (preserves layout caller zeroValid)
    layout.tape.unit.representation caller.initial caller.initialCode caller.initialFits (inputFits layout)
    fuel (admissible layout fuel) (initial_valid layout caller fuel) initialTime initialBound

theorem names (fuel slots : Nat)
    (localNames : NamesAccounted caller.continuation.code slots)
    (initialNames : NamesAccounted caller.initialCode.code slots) :
    WordIO.NamesAccounted ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)) (nameBudget layout zeroValid slots) :=
  CallerControl.program_names (step layout) (Fresh.port layout.tape) caller.advance caller.continuation caller.localFits
    (PrivateQuery.code layout.tape zeroValid) layout.tape.unit.representation caller.initial caller.initialCode caller.initialFits
    (inputFits layout) (by unfold nameBudget; omega)
    ((PrivateQuery.names layout.tape zeroValid).mono (by unfold nameBudget; omega))
    (localNames.mono (by unfold nameBudget; omega)) (initialNames.mono (by unfold nameBudget; omega)) fuel

/-- Time and memory describe the same actual execution, including stored code,
the initial buffers and every visited state, not just its final output. -/
theorem resources (fuel localTime initialTime slots : Nat)
    (localBound : ∀ value, caller.continuation.time value ≤ localTime)
    (initialBound : ∀ value, caller.initialCode.time value ≤ initialTime)
    (localNames : NamesAccounted caller.continuation.code slots)
    (initialNames : NamesAccounted caller.initialCode.code slots)
    (tape : RandomTape w) (value : layout.tape.unit.Value × Store layout) (valid : admissible layout fuel value)
    (before : State w) (holds : (input layout).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout caller zeroValid fuel).execute (Fresh.port layout.tape) .unit tape before)) :
    finished.time ≤ timeBudget layout zeroValid localTime initialTime fuel ∧
    ∃ answer ∈ support (source layout caller zeroValid fuel value), (CallerStep.output (step layout)).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)) before
          finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).registerSlots) ∧
          between.SupportBound (max buffers ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound) ∧ between.WellFormed ∧
          (((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound) ≤
              5 * codeBudget layout caller zeroValid fuel + 4 * nameBudget layout zeroValid slots +
                registers + 3 * buffers + before.liveMem buffers + timeBudget layout zeroValid localTime initialTime fuel := by
  have words := code_bound layout caller zeroValid fuel
  have named := names layout caller zeroValid fuel slots localNames initialNames
  have reserved : WordIO.NamesBound ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape))
      (nameBudget layout zeroValid slots + codeBudget layout caller zeroValid fuel) :=
    ⟨named.registers.trans (Nat.add_le_add_left words _), named.buffers.trans (Nat.add_le_add_left words _)⟩
  have checked := (refines layout caller zeroValid fuel).resources
    (time_bound layout caller zeroValid fuel localTime initialTime localBound initialBound) words reserved
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := checked
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler
