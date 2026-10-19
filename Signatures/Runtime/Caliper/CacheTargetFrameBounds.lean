import Signatures.Runtime.Caliper.CacheTargetFrame

/-! Resource bounds for final-request packing include all repeated copies of
the cache capacity and the literal fallback. No cache-size scan is uncharged. -/
namespace Signatures.Runtime.CaliperBackend.CacheTargetFrame
open Caliper BoundedSource
variable {w : Nat} {K F R : Type} (layout : CacheAccumulate.Layouts w K F R)

theorem result_bounded : (result layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.first_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; simp only [Layout.prod_words, CacheRead.output] at *; omega
theorem table_bounded : (table layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.first_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; simp only [Layout.prod_words, CacheRead.output] at *; omega
theorem target_bounded : (target layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals have := sizes layout; have := key_size layout; simp only [Layout.prod_words, context] at *; omega
theorem coefficient_bounded : (coefficient layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals have := sizes layout; have := layout.base_sizes; simp only [Layout.prod_words, context] at *; omega
theorem unit_bounded : (unit layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply (Implementation.constant_bounded _ _ _ _).mono
  all_goals simp only [LookupLayout.unit_words]; omega
theorem tableTail_bounded : (tableTail layout).BoundedBy (136 * layout.width) (442 * layout.width + 182) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (table_bounded layout) (unit_bounded layout)).mono
  all_goals simp only [LookupLayout.unit_words]; have := sizes layout; have := layout.base_sizes; omega
theorem saved_bounded : (saved layout).BoundedBy (136 * layout.width) (442 * layout.width + 182) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (coefficient_bounded layout) (result_bounded layout)).mono
  all_goals have := sizes layout; have := layout.base_sizes; simp only [Layout.prod_words, context] at *; omega

variable (fallback : layout.cache.value.Value)
theorem defaultValue_bounded : (defaultValue layout fallback).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply (Implementation.constant_bounded _ _ _ _).mono
  all_goals have := layout.base_sizes; omega
theorem valueTail_bounded : (valueTail layout fallback).BoundedBy (256 * layout.width) (832 * layout.width + 335) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (defaultValue_bounded layout fallback) (tableTail_bounded layout)).mono
  all_goals have := sizes layout; have := layout.base_sizes; simp only [Layout.prod_words, context] at *; omega
theorem request_bounded : (request layout fallback).BoundedBy (376 * layout.width) (1222 * layout.width + 488) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (target_bounded layout) (valueTail_bounded layout fallback)).mono
  all_goals have := sizes layout; have := key_size layout; simp only [Layout.prod_words, context] at *; omega
def timeBudget : Nat := 616 * layout.width
def codeBudget : Nat := 2002 * layout.width + 794
theorem pack_bounded : (pack layout fallback).BoundedBy (timeBudget layout) (codeBudget layout) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (request_bounded layout fallback) (saved_bounded layout)).mono
  all_goals dsimp only [timeBudget, codeBudget]; have := sizes layout; have := layout.sizes; omega
variable [DecidableEq K]
theorem implementation_bounded : (implementation layout fallback).BoundedBy (timeBudget layout) (codeBudget layout) :=
  ⟨fun value => (pack_bounded layout fallback).time_le ⟨value.val, value.property.1⟩,
    (pack_bounded layout fallback).code_le⟩
end Signatures.Runtime.CaliperBackend.CacheTargetFrame
