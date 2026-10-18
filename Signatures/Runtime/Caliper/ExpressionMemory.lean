import Signatures.Runtime.Caliper.ExpressionNames
import Signatures.Runtime.Caliper.WordFrames

/-! Complete memory budgets for accepted original expressions: stored code,
dense registers/descriptors, all initial buffer capacity, and dynamic growth.
The bound covers intermediate states and the final state of actual execution. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper BoundedSource

variable {w : Nat}

/-- The initial support bound makes this a sum over all initial capacity,
including caller-owned storage outside the represented input. -/
theorem LocalReach.total_memory_bound {cost : CostModel} {tape : RandomTape w} {code : Stmt w}
    {before after between : State w} {time : Nat} {net peak : Int}
    (execution : Caliper.Exec cost tape code before after time net peak)
    (visited : Caliper.Reaches cost tape code before between ∨ between = after)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers)
    (initialBuffers : before.SupportBound buffers) (initialWellFormed : before.WellFormed) :
    RegisterBound between (max registers (registerSlots code)) ∧
    between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
    (staticWords code registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
      staticWords code registers buffers + before.liveMem buffers + peak := by
  have initialMemory := liveMem_eq_of_supportBound initialBuffers (Nat.le_max_left buffers code.memBound)
  rcases visited with reached | rfl
  · refine ⟨?_, ?_, LocalReach.wellFormed reached initialWellFormed, ?_⟩
    · intro register outside
      rw [LocalReach.frame_reg reached (fun written => Nat.not_lt_of_ge ((Nat.le_max_right _ _).trans outside)
        (writes_lt_registerSlots written))]
      exact initialRegisters register ((Nat.le_max_left _ _).trans outside)
    · intro buffer outside
      rw [LocalReach.frame_cap reached (fun touched => Nat.not_lt_of_ge ((Nat.le_max_right _ _).trans outside)
        (Stmt.touches_lt_memBound touched))]
      exact initialBuffers buffer ((Nat.le_max_left _ _).trans outside)
    · have memory := intermediate_buffer_memory_bound execution reached (Nat.le_max_right buffers code.memBound)
      rw [initialMemory] at memory
      omega
  · refine ⟨registerBound_preserved execution initialRegisters,
      execution.supportBound_preserved
        (Stmt.touches_lt_of_memBound_le (Nat.le_max_right buffers code.memBound))
        (initialBuffers.mono (Nat.le_max_left buffers code.memBound)),
      execution.wellFormed_preserved initialWellFormed, ?_⟩
    have memory := buffer_memory_bound execution (Nat.le_max_right buffers code.memBound)
    rw [initialMemory] at memory
    omega

namespace BoundedSource.Budget

def staticMemory (budget : Budget) (primitiveSlots registers buffers : Nat) : Nat :=
  budget.words + max registers (primitiveSlots + budget.words) +
    3 * max buffers (primitiveSlots + budget.words)

theorem staticMemory_le (budget : Budget) (primitiveSlots registers buffers : Nat) :
    budget.staticMemory primitiveSlots registers buffers ≤
      5 * budget.words + 4 * primitiveSlots + registers + 3 * buffers := by
  unfold staticMemory
  omega

def memory (budget : Budget) (primitiveSlots registers buffers initialCapacity : Nat) : Nat :=
  budget.staticMemory primitiveSlots registers buffers + initialCapacity + budget.time

end BoundedSource.Budget

namespace SourceExpression

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    {P : Primitives base Op} {hw : 16 < 2 ^ w}
    {Γ : List (Ty Atom)} {a : Ty Atom} {expression : Expr Op Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (certificate : Compilation P .unit hw expression input output) (bounds : certificate.LocalBounds)
    {slots : Nat} (names : certificate.PrimitiveNames slots)
    (implementation : Implementation .unit input output (expression.denote P))
    (compiled : certificate.compile (by decide) = some implementation)

include names compiled

theorem Compilation.nameBounds :
    NamesBound implementation.program.code (slots + (certificate.budget bounds).words) :=
  NamesBound.mono (certificate.names slots names implementation compiled)
    (Nat.add_le_add_left (certificate.bounded bounds implementation compiled).code_le slots)

theorem Compilation.staticMemory_bound (registers buffers : Nat) :
    staticWords implementation.program.code registers buffers ≤
      (certificate.budget bounds).staticMemory slots registers buffers := by
  have nameBound := certificate.nameBounds bounds names implementation compiled
  exact Nat.add_le_add
    (Nat.add_le_add (certificate.bounded bounds implementation compiled).code_le
      (max_le_max le_rfl nameBound.registers))
    (Nat.mul_le_mul_left 3 (max_le_max le_rfl nameBound.buffers))

/-- No assumption about a finished expression's resource use is needed. The
only supplied budgets concern primitive code and final-layout conversions. -/
theorem Compilation.memoryBound (tape : RandomTape w) (environment : input.Value) (before : State w)
    (represented : input.representation.Holds environment before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape implementation.program.code before after
        (implementation.program.time environment) net peak ∧
      output.representation.Holds ⟨expression.denote P environment.val, implementation.preserves environment.val environment.property⟩ after ∧
      implementation.program.time environment ≤ (certificate.budget bounds).time ∧
      ∀ between, (Caliper.Reaches .unit tape implementation.program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots implementation.program.code)) ∧
        between.SupportBound (max buffers implementation.program.code.memBound) ∧ between.WellFormed ∧
        (staticWords implementation.program.code registers buffers : Int) +
          between.liveMem (max buffers implementation.program.code.memBound) ≤
            (certificate.budget bounds).memory slots registers buffers (before.liveMem buffers) := by
  obtain ⟨after, net, peak, execution, outputValue, elapsed, _, peakBound⟩ :=
    certificate.exec_bounded bounds implementation compiled tape environment before represented
  refine ⟨after, net, peak, execution, outputValue, elapsed, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ :=
    LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers represented.2.2.1
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  have staticBound := certificate.staticMemory_bound bounds names implementation compiled registers buffers
  simp only [Budget.memory, Nat.cast_add]
  omega

end SourceExpression
end Signatures.Runtime.CaliperBackend
