import Proofs.Runtime.Caliper.ListSnoc

/-! Uniform append budgets charge both actual reversals, the generated pairing,
temporary capacity growth, and the final copy that restores the input capacity. -/
namespace Signatures.Runtime.CaliperBackend.ListSnoc
open Caliper BoundedSource
variable {w : Nat} {A : Type} (layout : Layouts w A)

def timeBudget : Nat := ListReverse.timeBudget layout.reversal + ListReverse.timeBudget layout.extended + 144 * layout.width + 8
def codeBudget : Nat := ListReverse.codeBudget layout.reversal + ListReverse.codeBudget layout.extended + 480 * layout.width + 256

theorem entry_bounded : (entry layout).BoundedBy
    (8 * layout.entry.representation.encoding.words) (26 * layout.entry.representation.encoding.words + 14) :=
  Implementation.first_boundedBy _ _ _ _
theorem reversed_bounded : (reversed layout).BoundedBy
    (8 * layout.list.representation.encoding.words + ListReverse.timeBudget layout.reversal)
    (26 * layout.list.representation.encoding.words + ListReverse.codeBudget layout.reversal + 15) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (ListReverse.bounded layout.reversal)).mono
  all_goals dsimp only [Layouts.list]; omega
theorem prepare_bounded : (prepare layout).BoundedBy
    (ListReverse.timeBudget layout.reversal + 120 * layout.width)
    (ListReverse.codeBudget layout.reversal + 390 * layout.width + 153) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (entry_bounded layout) (reversed_bounded layout)).mono
  all_goals have := layout.sizes; omega
theorem prepend_bounded : (prepend layout).BoundedBy (8 * layout.width + 5) (26 * layout.width + 38) := by
  apply (ListData.cons_boundedBy layout.entry layout.capacity layout.wordFits layout.countFits layout.grown.representation.fits).mono
  all_goals
    have bound := layout.sizes.2.2.1
    change 1 + (layout.capacity + 1) * layout.entry.representation.encoding.words ≤ layout.width at bound
    omega
theorem appended_bounded : (appended layout).BoundedBy
    (ListReverse.timeBudget layout.reversal + ListReverse.timeBudget layout.extended + 128 * layout.width + 5)
    (ListReverse.codeBudget layout.reversal + ListReverse.codeBudget layout.extended + 416 * layout.width + 193) := by
  apply ((((prepare_bounded layout).then (prepend_bounded layout)).then (ListReverse.bounded layout.extended)).castFunction _).mono <;> omega
theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  have admitted := ((appended_bounded layout).restrictInput (fun input => input.2.length < layout.capacity)).restrictOutput
    (fun values => values.length ≤ layout.capacity) (by
      intro input valid
      simp only [List.length_append, List.length_singleton]
      exact Nat.succ_le_of_lt valid.2)
  apply (admitted.then (ListData.narrow_boundedBy layout.entry (layout.capacity + 1) layout.capacity (by omega)
    layout.wordFits layout.countFits layout.grown.representation.fits)).mono
  all_goals
    have bound := layout.sizes.2.1
    change 1 + layout.capacity * layout.entry.representation.encoding.words ≤ layout.width at bound
    dsimp only [timeBudget, codeBudget]
    omega

end Signatures.Runtime.CaliperBackend.ListSnoc
