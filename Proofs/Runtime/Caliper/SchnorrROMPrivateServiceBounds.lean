import Proofs.Runtime.Caliper.SchnorrROMPrivateService

/-! Complete service resources include the executed scalar/store output
conversion. Bounds concern the same execution as the source refinement and
count all live states, initial data, code, registers and descriptors. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Service
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {F C : Type} [Zero F] (layout : Layouts w F C)
    (caller : Caller layout) (zeroValid : layout.tape.scalar.valid 0)

def timeBudget (localTime initialTime fuel : Nat) :=
  PrivateSampler.timeBudget layout zeroValid localTime initialTime fuel + 68 * CallerStep.width (step layout) + 4
def codeBudget (fuel : Nat) :=
  PrivateSampler.codeBudget layout caller zeroValid fuel + 325 * CallerStep.width (step layout) + 189

theorem time_bound (fuel localTime initialTime : Nat)
    (localBound : ∀ value, caller.continuation.time value ≤ localTime)
    (initialBound : ∀ value, caller.initialCode.time value ≤ initialTime) :
    Interactive.TimeBoundOn (ready layout fuel) (Fresh.port layout.tape) .unit (Read.tapes layout.tape).representation
      (code layout caller zeroValid fuel) (timeBudget layout zeroValid localTime initialTime fuel) := by
  have bound := Interactive.TimeBoundOn.seq (PrivateSampler.refines layout caller zeroValid fuel)
    (PrivateSampler.time_bound layout caller zeroValid fuel localTime initialTime localBound initialBound)
    ((Interactive.TimeBound.compute (port := Fresh.port layout.tape) (cost := .unit)
      (Finish.program layout ⟨0, zeroValid⟩) _ (Finish.time layout ⟨0, zeroValid⟩)).on (fun _ => True))
    (by intros; trivial)
  intro tape saved valid before holds finished reached
  have timed := bound tape (unit layout, saved) valid before holds finished reached
  exact timed.trans (by unfold timeBudget; omega)

theorem code_bound (fuel : Nat) :
    ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).descriptionWords ≤ codeBudget layout caller zeroValid fuel := by
  have sampled := PrivateSampler.code_bound layout caller zeroValid fuel
  have converted := Finish.words layout ⟨0, zeroValid⟩
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

theorem descriptionFits (fuel : Nat) : ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).DescriptionFits :=
  .seq layout.tape.wordFits (PrivateSampler.descriptionFits layout caller zeroValid fuel)
    (.compute (Finish.program layout ⟨0, zeroValid⟩).description_fits)

theorem names (fuel slots : Nat) (localNames : NamesAccounted caller.continuation.code slots)
    (initialNames : NamesAccounted caller.initialCode.code slots) :
    WordIO.NamesAccounted ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape))
      (PrivateSampler.nameBudget layout zeroValid slots) :=
  (PrivateSampler.names layout caller zeroValid fuel slots localNames initialNames).seq
    (.compute ((Finish.names layout ⟨0, zeroValid⟩).mono (by unfold PrivateSampler.nameBudget; omega)))

theorem resources (fuel localTime initialTime slots : Nat)
    (localBound : ∀ value, caller.continuation.time value ≤ localTime)
    (initialBound : ∀ value, caller.initialCode.time value ≤ initialTime)
    (localNames : NamesAccounted caller.continuation.code slots) (initialNames : NamesAccounted caller.initialCode.code slots)
    (tape : RandomTape w) (saved : Store layout) (valid : ready layout fuel saved)
    (before : State w) (holds : (Read.tapes layout.tape).representation.Holds saved before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout caller zeroValid fuel).execute (Fresh.port layout.tape) .unit tape before)) :
    finished.time ≤ timeBudget layout zeroValid localTime initialTime fuel ∧
    ∃ answer ∈ support (source layout caller zeroValid fuel saved), (Reply.scalarOutput layout.tape).representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)) before
          finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).registerSlots) ∧
          between.SupportBound (max buffers ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound) ∧ between.WellFormed ∧
          (((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape)).memBound) ≤
              5 * codeBudget layout caller zeroValid fuel + 4 * PrivateSampler.nameBudget layout zeroValid slots +
                registers + 3 * buffers + before.liveMem buffers + timeBudget layout zeroValid localTime initialTime fuel := by
  have words := code_bound layout caller zeroValid fuel
  have named := names layout caller zeroValid fuel slots localNames initialNames
  have reserved : WordIO.NamesBound ((code layout caller zeroValid fuel).lower (Fresh.port layout.tape))
      (PrivateSampler.nameBudget layout zeroValid slots + codeBudget layout caller zeroValid fuel) :=
    ⟨named.registers.trans (Nat.add_le_add_left words _), named.buffers.trans (Nat.add_le_add_left words _)⟩
  have checked := (refines layout caller zeroValid fuel).resources
    (time_bound layout caller zeroValid fuel localTime initialTime localBound initialBound) words reserved
    tape saved valid before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨elapsed, answer, supported, output, execution, visitedBound⟩ := checked
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := visitedBound between visited
  exact ⟨registerBound, bufferBound, wellFormed, by push_cast at memory; omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Service
