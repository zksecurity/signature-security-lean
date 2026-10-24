import Proofs.Runtime.Caliper.SourceBounds
import Proofs.Runtime.Caliper.WordFrames

/-! The compiled program's complete machine-memory account: stored code, dense
register slots, buffer descriptors, initial capacity and uniform dynamic growth.
All instruction-boundary states of the same actual execution satisfy the bound.
Word/address acceptance and flat-memory/CPU adequacy are separate obligations.
-/

namespace Signatures.Runtime.CaliperBackend.SourceCompilation

open Caliper OracleComp OracleSpec PFunctor BoundedSource

universe v u

variable {w : Nat} {I : Type} {spec : OracleSpec I}
    {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
    {Q : QuantitativeStepClass.{0, v, u} C} {sourceIface : BackendProgram.Interface (C := C) spec}
    {targetIface : Interface w spec} {cost : WordIO.Costs} {hw : 16 < 2 ^ w}
    {A B : Type} {a : C.Str A} {b : C.Str B}
    {source : BackendProgram.Code Q spec sourceIface a b} {input : Layout w A} {output : Layout w B}

def Compilation.memoryBudget (code : Compilation targetIface cost hw source input output)
    (bounds : code.LocalBounds) (before : State w) (registers buffers : Nat) : Nat :=
  (code.compile.lower targetIface.port).staticWords registers buffers +
    before.liveMem (max buffers (code.compile.lower targetIface.port).memBound) + code.timeBudget bounds

/-- The support hypothesis selects a particular reachable result; the returned
execution witnesses its actual trace and resource profile. The memory conclusion
covers every state visited by that execution, not a run with different replies. -/
theorem Compilation.memoryBound (code : Compilation targetIface cost hw source input output)
    (bounds : code.LocalBounds) (allocation : 1 ≤ cost.machine.allocPerWord)
    (tape : RandomTape w) (value : input.Value) (before : State w)
    (holds : input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support (code.compile.execute targetIface.port cost tape before)) :
    ∃ execution : WordIO.Exec cost tape (code.compile.lower targetIface.port) before finished.state
        finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        RegisterBound between (max registers (code.compile.lower targetIface.port).registerSlots) ∧
        between.SupportBound (max buffers (code.compile.lower targetIface.port).memBound) ∧ between.WellFormed ∧
        ((code.compile.lower targetIface.port).staticWords registers buffers : Int) +
          between.liveMem (max buffers (code.compile.lower targetIface.port).memBound) ≤
            code.memoryBudget bounds before registers buffers := by
  have peakBound := (code.resources bounds allocation tape value before holds finished reached).2
  obtain ⟨answer, _, result, equal, _, _, execution⟩ := (code.correct allocation tape value before holds).right_support reached
  cases Option.some.inj equal
  refine ⟨execution, ?_⟩
  intro between visited
  obtain ⟨registersBound, buffersBound, wellFormed, memory⟩ :=
    visited.total_memory_bound registers buffers initialRegisters initialBuffers holds.2.2.1
  refine ⟨registersBound, buffersBound, wellFormed, ?_⟩
  simp only [memoryBudget, Nat.cast_add]
  omega

end Signatures.Runtime.CaliperBackend.SourceCompilation
