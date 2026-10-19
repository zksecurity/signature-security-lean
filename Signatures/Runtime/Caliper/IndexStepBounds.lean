import Signatures.Runtime.Caliper.IndexStep
import Signatures.Runtime.Caliper.BranchBudgets

/-! Scan-body budgets derived from the constructed projections, constants,
comparisons, saturating subtraction and two stored conditionals. -/

namespace Signatures.Runtime.CaliperBackend.ListIndex
open Caliper BoundedSource
variable {w : Nat} {V : Type} (layout : Layouts w V)

theorem current_bounded : (current layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals simp only [Layout.prod_words, Layouts.unit_words]; have := layout.sizes; omega
theorem entry_bounded : (entry layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) :=
  (Implementation.first_boundedBy _ _ _ _).mono (Nat.mul_le_mul_left _ layout.value_le) (by have := layout.value_le; omega)
theorem remaining_bounded : (remaining layout).BoundedBy (16 * layout.width + 8) (52 * layout.width + 70) := by
  apply ((current_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals simp only [Layouts.counter_words]; omega
theorem payload_bounded : (payload layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((current_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; omega
theorem found_bounded : (found layout).BoundedBy (24 * layout.width + 8) (78 * layout.width + 85) := by
  apply ((payload_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals simp only [Layouts.boolean_words]; omega
theorem zero_bounded : (zero layout).BoundedBy 8 40 := Implementation.constant_bounded _ _ _ _
theorem one_bounded : (one layout).BoundedBy 8 40 := Implementation.constant_bounded _ _ _ _
theorem yes_bounded : (yes layout).BoundedBy 8 40 := Implementation.constant_bounded _ _ _ _

theorem zeroArgs_bounded : (zeroArgs layout).BoundedBy (120 * layout.width + 68) (390 * layout.width + 403) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (remaining_bounded layout) (zero_bounded layout)).mono
  all_goals simp only [Layouts.counter_words]; have := layout.sizes; omega
theorem zeroTest_bounded : (zeroTest layout).BoundedBy (120 * layout.width + 74) (390 * layout.width + 431) := by
  have primitive : (Natural.equal .unit layout.indexBound layout.indexBound layout.wordFits layout.indexFits layout.indexFits).BoundedBy 6 27 :=
    ⟨fun _ => le_rfl, (WordBinary.descriptionWords_eq .eq).le⟩
  exact ((zeroArgs_bounded layout).then primitive).mono (by omega) (by omega)
theorem subtractionArgs_bounded : (subtractionArgs layout).BoundedBy (120 * layout.width + 68) (390 * layout.width + 403) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (remaining_bounded layout) (one_bounded layout)).mono
  all_goals
    have size : (oneLayout layout).representation.encoding.words = 1 := rfl
    simp only [Layouts.counter_words, size]
    have := layout.sizes
    omega
theorem decrement_bounded : (decrement layout).BoundedBy (120 * layout.width + 76) (390 * layout.width + 442) := by
  have primitive : (Natural.subtract .unit layout.indexBound 2 layout.wordFits layout.indexFits (by have := layout.wordFits; omega)).BoundedBy 8 38 :=
    ⟨fun value => (Natural.subtract_time_unit _ _ _ _ _ value).le, Saturating.descriptionWords_eq.le⟩
  exact ((subtractionArgs_bounded layout).then primitive).mono (by omega) (by omega)

theorem selected_bounded : (selected layout).BoundedBy (128 * layout.width + 44) (416 * layout.width + 295) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (yes_bounded layout) (entry_bounded layout)).mono
  all_goals simp only [Layouts.boolean_words]; have := layout.sizes; have := layout.value_le; omega
theorem hit_bounded : (hit layout).BoundedBy (248 * layout.width + 88) (806 * layout.width + 576) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (zero_bounded layout) (selected_bounded layout)).mono
  all_goals simp only [Layouts.counter_words]; have := layout.sizes; omega
theorem miss_bounded : (miss layout).BoundedBy (264 * layout.width + 112) (858 * layout.width + 727) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (decrement_bounded layout) (payload_bounded layout)).mono
  all_goals simp only [Layouts.counter_words]; have := layout.sizes; omega
theorem search_bounded : (search layout).BoundedBy (784 * layout.width + 317) (2600 * layout.width + 2038) := by
  apply (Implementation.checkedBranch_boundedBy _ _ _ layout.bodyDuplicate layout.bodyTag _ _ _ _ _ _
    (zeroTest_bounded layout) (hit_bounded layout) (miss_bounded layout) (search layout)
    (Option.eq_some_of_isSome (search_accepted layout))).mono
  all_goals have := layout.sizes; omega
theorem body_bounded : (body layout).BoundedBy (1000 * layout.width + 400) (3300 * layout.width + 2500) := by
  have bound := Implementation.checkedBranch_boundedBy _ _ _ layout.bodyDuplicate layout.bodyTag _ _ _ _ _ _
    (found_bounded layout) (current_bounded layout) (search_bounded layout)
    ((bodyCompiled layout).get (body_accepted layout)) (Option.eq_some_of_isSome (body_accepted layout))
  constructor
  · intro value
    exact (bound.time_le value).trans (by have := layout.sizes; omega)
  · exact bound.code_le.trans (by have := layout.sizes; omega)

end Signatures.Runtime.CaliperBackend.ListIndex
