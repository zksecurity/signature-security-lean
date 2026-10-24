import Proofs.Runtime.Caliper.CacheAccumulateFinish

/-! Bounds for the executed continuation. Only its local arithmetic routine
supplies a budget; projections, argument construction and cache retention are
charged here. -/

namespace Signatures.Runtime.CaliperBackend.CacheAccumulate
open Caliper BoundedSource
variable {w : Nat} {K F R : Type} (layout : Layouts w K F R)

theorem answer_bounded : (answer layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.first_boundedBy (CacheRead.output layout.cache) layout.saved layout.cache.wordFits _).then
    (Implementation.first_boundedBy layout.cache.value layout.cache.lookup.table layout.cache.wordFits _)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; omega
theorem table_bounded : (table layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.first_boundedBy (CacheRead.output layout.cache) layout.saved layout.cache.wordFits _).then
    (Implementation.second_boundedBy layout.cache.value layout.cache.lookup.table layout.cache.wordFits _)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; omega
theorem coefficient_bounded : (coefficient layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy (CacheRead.output layout.cache) layout.saved layout.cache.wordFits _).then
    (Implementation.first_boundedBy layout.coefficient layout.cache.value layout.cache.wordFits _)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; omega
theorem accumulator_bounded : (accumulator layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy (CacheRead.output layout.cache) layout.saved layout.cache.wordFits _).then
    (Implementation.second_boundedBy layout.coefficient layout.cache.value layout.cache.wordFits _)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; omega
theorem operands_bounded : (operands layout).BoundedBy (136 * layout.width) (442 * layout.width + 182) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (answer_bounded layout) (accumulator_bounded layout)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; omega
theorem arguments_bounded : (arguments layout).BoundedBy (256 * layout.width) (832 * layout.width + 335) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (coefficient_bounded layout) (operands_bounded layout)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; omega

variable {combine : F × (R × R) → R} (update : Implementation .unit layout.combine layout.cache.value combine)
    {updateTime updateCode : Nat} (bound : update.BoundedBy updateTime updateCode)
    {slots : Nat} (updateBuffers : update.program.code.memBound ≤ slots) (reserve : slots + 2 < 2 ^ w)
include bound in
theorem updated_bounded : (updated layout update).BoundedBy (256 * layout.width + updateTime)
    (832 * layout.width + 336 + updateCode) := by
  apply ((arguments_bounded layout).then bound).mono <;> omega
include bound in
theorem finish_bounded : (finish layout update updateBuffers reserve).BoundedBy
    (376 * layout.width + updateTime) (1222 * layout.width + 489 + updateCode) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (updated_bounded layout update bound) (table_bounded layout)).mono
  all_goals have := layout.sizes; have := layout.base_sizes; omega

end Signatures.Runtime.CaliperBackend.CacheAccumulate
