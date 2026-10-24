import Proofs.Runtime.Caliper.SchnorrAGMHistories

/-! Whole signing-history budgets include both append programs and every copy
needed to retain the cache, signature and flags. Complete memory is bounded on
the same execution that returns the original source history update. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def timeBudget : Nat := ListSnoc.timeBudget layout.basisAppend + ListSnoc.timeBudget layout.signedAppend + 3072 * layout.width
def codeBudget : Nat := ListSnoc.codeBudget layout.basisAppend + ListSnoc.codeBudget layout.signedAppend + 10240 * layout.width + 2048

theorem updatedSignedFlags_bounded : (updatedSignedFlags layout).BoundedBy
    (ListSnoc.timeBudget layout.signedAppend + 1056 * layout.width)
    (ListSnoc.codeBudget layout.signedAppend + 3432 * layout.width + 519) := by
  apply (combine_bounded layout _ _ _ _ _ _ (appendSigned_bounded layout) (selection_bounded layout).2.2.2.2.2.2).mono <;> omega
theorem updatedMetadata_bounded : (updatedMetadata layout).BoundedBy
    (ListSnoc.timeBudget layout.basisAppend + ListSnoc.timeBudget layout.signedAppend + 1968 * layout.width)
    (ListSnoc.codeBudget layout.basisAppend + ListSnoc.codeBudget layout.signedAppend + 6396 * layout.width + 948) := by
  apply (combine_bounded layout _ _ _ _ _ _ (appendBasis_bounded layout) (updatedSignedFlags_bounded layout)).mono <;> omega
theorem updatedSaved_bounded : (updatedSaved layout).BoundedBy
    (ListSnoc.timeBudget layout.basisAppend + ListSnoc.timeBudget layout.signedAppend + 2424 * layout.width)
    (ListSnoc.codeBudget layout.basisAppend + ListSnoc.codeBudget layout.signedAppend + 7878 * layout.width + 1162) := by
  apply (combine_bounded layout _ _ _ _ _ _ (selection_bounded layout).2.1 (updatedMetadata_bounded layout)).mono <;> omega
theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  apply (combine_bounded layout _ _ _ _ _ _ (selection_bounded layout).1 (updatedSaved_bounded layout)).mono
  all_goals dsimp only [timeBudget, codeBudget]; omega

theorem static_bound (registers buffers : Nat) : staticWords (implementation layout).program.code registers buffers ≤
    5 * codeBudget layout + registers + 3 * buffers := by
  have stored := (bounded layout).code_le
  have registersBound := (names layout 0).registers
  have buffersBound := (names layout 0).buffers
  unfold staticWords
  omega

theorem resources (tape : RandomTape w) (input : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds input before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time input) net peak ∧
      layout.output.representation.Holds
        ⟨Signatures.Runtime.SchnorrAGM.Native.Signing.historiesValue input.val, (implementation layout).preserves input.val input.property⟩ after ∧
      (implementation layout).program.time input ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
          5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, _, _⟩ := (bounded layout).exec (by decide) tape input before holds
  refine ⟨after, net, peak, execution, output, elapsed, ?_⟩
  intro between visited
  have memory := (LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1).2.2.2
  have stored := static_bound layout registers buffers
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
