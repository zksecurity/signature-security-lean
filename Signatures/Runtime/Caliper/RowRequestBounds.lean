import Signatures.Runtime.Caliper.RowRequest

/-! Bounds and generated names for actual row request construction. -/
namespace Signatures.Runtime.CaliperBackend.RowRequest
open Caliper BoundedSource
variable {w : Nat} {K G F R : Type} (layout : Layouts w K G F R)
    (default : layout.accumulation.cache.value.Value)

theorem row_bounded : (row layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply ((Implementation.first_boundedBy layout.row layout.state layout.accumulation.cache.wordFits layout.raw.representation.fits).restrictInput layout.ready).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    simp only [Layouts.row_words]
    dsimp only [CacheLayout.lookup] at *
    omega

theorem state_bounded : (state layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply ((Implementation.second_boundedBy layout.row layout.state layout.accumulation.cache.wordFits layout.raw.representation.fits).restrictInput layout.ready).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    simp only [Layouts.state_words]
    dsimp only [CacheLayout.lookup] at *
    omega

theorem token_bounded : (token layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((row_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    simp only [Layouts.token_words]
    dsimp only [CacheLayout.lookup] at *
    omega

theorem message_bounded : (message layout).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((token_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    dsimp only [CacheLayout.lookup] at *
    omega

theorem coefficient_bounded : (coefficient layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((row_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    dsimp only [CacheLayout.lookup] at *
    omega

theorem accumulator_bounded : (accumulator layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((state_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    dsimp only [CacheLayout.lookup] at *
    omega

theorem table_bounded : (table layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((state_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    dsimp only [CacheLayout.lookup] at *
    omega

theorem tableTail_bounded : (tableTail layout).BoundedBy (104 * layout.width) (338 * layout.width + 167) := by
  have unitWords : (DataImplementation.unitLayout w).representation.encoding.words = 0 := rfl
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (table_bounded layout) (DataImplementation.unit_boundedBy _ _)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    simp only [Layouts.input_words, Layouts.raw_words, Layouts.row_words, Layouts.state_words]
    dsimp only [CacheLayout.lookup] at *
    omega

theorem valueTail_bounded : (valueTail layout default).BoundedBy (216 * layout.width) (702 * layout.width + 305) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (Implementation.constant_bounded _ _ _ _) (tableTail_bounded layout)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    simp only [Layouts.input_words, Layouts.raw_words, Layouts.row_words, Layouts.state_words, LookupLayout.tableTail_words]
    dsimp only [CacheLayout.lookup] at *
    omega

theorem saved_bounded : (saved layout).BoundedBy (136 * layout.width) (442 * layout.width + 182) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (coefficient_bounded layout) (accumulator_bounded layout)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    simp only [Layouts.input_words, Layouts.raw_words, Layouts.row_words, Layouts.state_words]
    dsimp only [CacheLayout.lookup] at *
    omega


variable [DecidableEq K]
theorem cacheArguments_bounded : (cacheArguments layout default).BoundedBy (344 * layout.width) (1118 * layout.width + 473) := by
  apply ((Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (message_bounded layout) (valueTail_bounded layout default)).restrictOutput layout.accumulation.cache.admissible (fun _ valid _ => valid.2)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have e := layout.width_eq
    simp only [Layouts.input_words, Layouts.raw_words, Layouts.row_words, Layouts.state_words, LookupLayout.valueTail_words]
    dsimp only [CacheLayout.lookup] at *
    omega

theorem prepare_bounded : (prepare layout default).BoundedBy (584 * layout.width) (1898 * layout.width + 779) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (cacheArguments_bounded layout default) (saved_bounded layout)).mono
  all_goals
    have h := layout.sizes
    have b := layout.accumulation.base_sizes
    have s := layout.accumulation.sizes
    have inputWords : layout.accumulation.cache.input.representation.encoding.words = layout.accumulation.cache.lookup.width := LookupLayout.input_words _
    have e := layout.width_eq
    simp only [Layouts.input_words, Layouts.raw_words, Layouts.row_words, Layouts.state_words, CacheAccumulate.Layouts.saved_words]
    dsimp only [CacheLayout.lookup] at *
    omega

end Signatures.Runtime.CaliperBackend.RowRequest
