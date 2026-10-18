import Signatures.Runtime.Caliper.ExpressionMemory

/-! Complete memory bounds from the time/code and name budgets of a constructed
local implementation. Initial capacity includes all caller-owned buffers. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper

variable {w : Nat} {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    {implementation : Implementation .unit input output f} {time words slots : Nat}

theorem Implementation.BoundedBy.staticMemory (bound : implementation.BoundedBy time words)
    (names : NamesAccounted implementation.program.code slots) (registers buffers : Nat) :
    staticWords implementation.program.code registers buffers ≤ 5 * words + 4 * slots + registers + 3 * buffers := by
  have codeBound := bound.code_le
  rcases names with ⟨registerBound, bufferBound⟩
  unfold staticWords
  omega

/-- The same actual execution computes the specified output and satisfies the
bound at every intermediate state, including dense names and stored code. -/
theorem Implementation.BoundedBy.memoryBound (bound : implementation.BoundedBy time words)
    (names : NamesAccounted implementation.program.code slots)
    (tape : RandomTape w) (value : input.Value) (before : State w)
    (represented : input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape implementation.program.code before after
        (implementation.program.time value) net peak ∧
      output.representation.Holds ⟨f value.val, implementation.preserves value.val value.property⟩ after ∧
      implementation.program.time value ≤ time ∧
      ∀ between, (Caliper.Reaches .unit tape implementation.program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots implementation.program.code)) ∧
        between.SupportBound (max buffers implementation.program.code.memBound) ∧ between.WellFormed ∧
        (staticWords implementation.program.code registers buffers : Int) +
          between.liveMem (max buffers implementation.program.code.memBound) ≤
            5 * words + 4 * slots + registers + 3 * buffers + before.liveMem buffers + time := by
  obtain ⟨after, net, peak, execution, outputValue, elapsed, _, peakBound⟩ :=
    bound.exec (by decide) tape value before represented
  refine ⟨after, net, peak, execution, outputValue, elapsed, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ :=
    LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers represented.2.2.1
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  have staticBound := bound.staticMemory names registers buffers
  omega

end Signatures.Runtime.CaliperBackend.BoundedSource
