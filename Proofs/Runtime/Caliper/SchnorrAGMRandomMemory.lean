import Proofs.Runtime.Caliper.SchnorrAGMRandomBounds

/-! Complete memory for the same source-correct randomness execution, including
stored program, caller memory and every state visited by the actual query. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
open Caliper BoundedSource OracleComp OracleSpec
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)

theorem resources (tape : RandomTape w) (args : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds args before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout).execute layout.port .unit tape before)) :
    finished.time ≤ timeBudget layout ∧ ∃ answer ∈ support (source layout args),
      layout.output.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout).lower layout.port)
        before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers ((code layout).lower layout.port).registerSlots) ∧
          between.SupportBound (max buffers ((code layout).lower layout.port).memBound) ∧ between.WellFormed ∧
          (((code layout).lower layout.port).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout).lower layout.port).memBound) ≤
              5 * codeBudget layout + 20 + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  have accounted := names layout
  have stored := code_bound layout
  have named : WordIO.NamesBound ((code layout).lower layout.port) (5 + codeBudget layout) :=
    ⟨accounted.registers.trans (Nat.add_le_add_left stored _), accounted.buffers.trans (Nat.add_le_add_left stored _)⟩
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    (refines layout).resources (time_bound layout) stored named tape args before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, result, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ := bounds between visited
  exact ⟨registerBound, bufferBound, wellFormed, by omega⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
