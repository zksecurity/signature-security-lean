import Signatures.Runtime.Caliper.CoronResponseNames
import Signatures.Runtime.Caliper.ImplementationMemory

/-! Complete memory bounds for the actual Coron response executions. Stored
code, primitive and generated names, initial capacities and intermediate copies
are all included in the same run that produces the specified response. -/
namespace Signatures.Runtime.CaliperBackend.CoronResponse
open Caliper BoundedSource
variable {w qS : Nat} {F G : Type} [SMul F G] [Add G] [Zero G]
    (layout : Layouts w F G qS) (zeroValid : layout.point.valid 0)
    (scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2))
    (add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2))
    {scaleTime scaleWords addTime addWords slots : Nat}
    (scaleBound : scale.BoundedBy scaleTime scaleWords) (addBound : add.BoundedBy addTime addWords)
    (scaleNames : NamesBound scale.program.code slots) (addNames : NamesBound add.program.code slots)
    (reserve : slots + 3 < 2 ^ w)

include scaleBound addBound addNames in
theorem reply_memoryBound (signing : Bool) (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (represented : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, ∃ result : layout.point.Value,
      Caliper.Exec .unit tape (reply layout zeroValid scale add scaleNames.buffers reserve signing).program.code before after
        ((reply layout zeroValid scale add scaleNames.buffers reserve signing).program.time value) net peak ∧
      result.val = replyValue signing value.val ∧ layout.point.representation.Holds result after ∧
      (reply layout zeroValid scale add scaleNames.buffers reserve signing).program.time value ≤ timeBudget layout signing scaleTime addTime ∧
      ∀ between,
        (Caliper.Reaches .unit tape (reply layout zeroValid scale add scaleNames.buffers reserve signing).program.code before between ∨ between = after) →
          RegisterBound between (max registers (registerSlots (reply layout zeroValid scale add scaleNames.buffers reserve signing).program.code)) ∧
          between.SupportBound (max buffers (reply layout zeroValid scale add scaleNames.buffers reserve signing).program.code.memBound) ∧ between.WellFormed ∧
          (staticWords (reply layout zeroValid scale add scaleNames.buffers reserve signing).program.code registers buffers : Int) +
            between.liveMem (max buffers (reply layout zeroValid scale add scaleNames.buffers reserve signing).program.code.memBound) ≤
              5 * codeBudget layout signing scaleWords addWords + 4 * slots + registers + 3 * buffers +
                before.liveMem buffers + timeBudget layout signing scaleTime addTime := by
  obtain ⟨after, net, peak, execution, output, elapsed, memory⟩ :=
    (reply_bounded layout zeroValid scale scaleBound scaleNames.buffers reserve add addBound signing).memoryBound
      (reply_names layout slots zeroValid scale scaleNames.accounted scaleNames.buffers reserve add addNames.accounted signing)
      tape value before represented registers buffers initialRegisters initialBuffers
  exact ⟨after, net, peak, _, execution, rfl, output, elapsed, memory⟩

end Signatures.Runtime.CaliperBackend.CoronResponse
