import Proofs.Runtime.Caliper.BLSResponseNames
import Proofs.Runtime.Caliper.ImplementationMemory

/-! Actual BLS response executions agree with the original arithmetic source
and have derived total-memory bounds throughout the same execution. Only the
two named arithmetic routines supply implementations and resource bounds. -/

namespace Signatures.Runtime.CaliperBackend.BLSResponse

open Caliper BoundedSource

variable {w : Nat} {F G G₂ M : Type} [Field F] [AddCommGroup G] [Module F G]
    [AddCommGroup G₂] [Module F G₂] [DecidableEq F] [DecidableEq G] [DecidableEq G₂] [DecidableEq M]
    (layout : Layouts w F G) (cost : PrimitiveCosts)
    (scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2))
    (add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2))
    {scaleTime scaleWords addTime addWords slots : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (addBound : add.BoundedBy addTime addWords)
    (scaleNames : NamesBound scale.program.code slots) (addNames : NamesBound add.program.code slots)

include scaleBound scaleNames in
theorem good_memoryBound (signing : Bool) (tape : RandomTape w) (value : layout.config.Value) (before : State w)
    (represented : layout.config.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, ∃ result : layout.point.Value,
      Caliper.Exec .unit tape (good layout scale signing).program.code before after
        ((good layout scale signing).program.time value) net peak ∧
      result.val = (LazyAGM.goodResponse signing).denote (arithmetic F G G₂ M M cost) (value.val.1, value.val.2, ()) ∧
      layout.point.representation.Holds result after ∧
      (good layout scale signing).program.time value ≤ goodTime layout scaleTime ∧
      ∀ between, (Caliper.Reaches .unit tape (good layout scale signing).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (good layout scale signing).program.code)) ∧
        between.SupportBound (max buffers (good layout scale signing).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (good layout scale signing).program.code registers buffers : Int) +
          between.liveMem (max buffers (good layout scale signing).program.code.memBound) ≤
            5 * goodWords layout scaleWords + 4 * slots + registers + 3 * buffers + before.liveMem buffers + goodTime layout scaleTime := by
  obtain ⟨after, net, peak, execution, outputValue, elapsed, memory⟩ :=
    (good_bounded layout scale scaleBound signing).memoryBound (good_names layout slots scale scaleNames.accounted signing)
      tape value before represented registers buffers initialRegisters initialBuffers
  exact ⟨after, net, peak, _, execution, good_source cost signing value.val.1 value.val.2.1 value.val.2.2,
    outputValue, elapsed, memory⟩

variable (reserve : slots + 3 < 2 ^ w)

include scaleBound addBound in
theorem bad_memoryBound (signing : Bool) (tape : RandomTape w) (value : layout.badInput.Value) (before : State w)
    (represented : layout.badInput.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, ∃ result : layout.point.Value,
      Caliper.Exec .unit tape (bad layout scale add scaleNames.buffers reserve addNames.buffers signing).program.code before after
        ((bad layout scale add scaleNames.buffers reserve addNames.buffers signing).program.time value) net peak ∧
      result.val = (LazyAGM.badResponse signing).denote (arithmetic F G G₂ M M cost) (value.val.1, value.val.2, ()) ∧
      layout.point.representation.Holds result after ∧
      (bad layout scale add scaleNames.buffers reserve addNames.buffers signing).program.time value ≤ badTime layout signing scaleTime addTime ∧
      ∀ between,
        (Caliper.Reaches .unit tape (bad layout scale add scaleNames.buffers reserve addNames.buffers signing).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (bad layout scale add scaleNames.buffers reserve addNames.buffers signing).program.code)) ∧
        between.SupportBound (max buffers (bad layout scale add scaleNames.buffers reserve addNames.buffers signing).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (bad layout scale add scaleNames.buffers reserve addNames.buffers signing).program.code registers buffers : Int) +
          between.liveMem (max buffers (bad layout scale add scaleNames.buffers reserve addNames.buffers signing).program.code.memBound) ≤
            5 * badWords layout signing scaleWords addWords + 4 * slots + registers + 3 * buffers + before.liveMem buffers + badTime layout signing scaleTime addTime := by
  obtain ⟨after, net, peak, execution, outputValue, elapsed, memory⟩ :=
    (bad_bounded layout scale add scaleBound addBound scaleNames.buffers reserve addNames.buffers signing).memoryBound
      (bad_names layout slots scale add scaleNames.accounted addNames.accounted scaleNames.buffers reserve addNames.buffers signing)
      tape value before represented registers buffers initialRegisters initialBuffers
  exact ⟨after, net, peak, _, execution, bad_source cost signing value.val.1 value.val.2.1 value.val.2.2.1 value.val.2.2.2,
    outputValue, elapsed, memory⟩

end Signatures.Runtime.CaliperBackend.BLSResponse
