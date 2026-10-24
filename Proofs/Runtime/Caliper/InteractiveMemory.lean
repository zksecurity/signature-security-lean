import Proofs.Runtime.Caliper.InteractiveNames
import Proofs.Runtime.Caliper.WordFrames

/-! One complete resource account for a supported interactive execution. Source
output, execution time and every visited memory state refer to that same run. -/

namespace Signatures.Runtime.CaliperBackend
open Caliper OracleComp OracleSpec

variable {w : Nat}

theorem WordIO.NamesBound.staticMemory {code : WordIO.Code w} {slots words : Nat}
    (names : WordIO.NamesBound code slots) (stored : code.descriptionWords ≤ words) (registers buffers : Nat) :
    code.staticWords registers buffers ≤ words + 4 * slots + registers + 3 * buffers := by
  have registersBound := names.registers
  have buffersBound := names.buffers
  unfold WordIO.Code.staticWords
  omega

namespace Interactive
variable {I A B : Type} {spec : OracleSpec I} {port : Port w spec}
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {code : Code w} {time words slots : Nat}

theorem Refines.resources (refined : Refines port .unit input output source code)
    (bounded : TimeBound port .unit input code time)
    (stored : (code.lower port).descriptionWords ≤ words) (names : WordIO.NamesBound (code.lower port) slots)
    (tape : RandomTape w) (value : A) (before : State w) (holds : input.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support (code.execute port .unit tape before)) :
    finished.time ≤ time ∧ ∃ answer ∈ support (source value), output.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower port).memBound) ∧ between.WellFormed ∧
          ((code.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower port).memBound) ≤
            words + 4 * slots + registers + 3 * buffers + before.liveMem buffers + time := by
  have elapsed := bounded tape value before holds finished reached
  have peak := bounded.bufferPeak refined (by decide) tape value before holds finished reached
  obtain ⟨answer, supported, result, equal, output, _, execution⟩ := (refined tape value before holds).right_support reached
  cases Option.some.inj equal
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ :=
    visited.total_memory_bound registers buffers initialRegisters initialBuffers holds.2.2.1
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  have staticBound := names.staticMemory stored registers buffers
  have initialMemory := liveMem_eq_of_supportBound initialBuffers (Nat.le_max_left buffers (code.lower port).memBound)
  omega

end Interactive
end Signatures.Runtime.CaliperBackend
