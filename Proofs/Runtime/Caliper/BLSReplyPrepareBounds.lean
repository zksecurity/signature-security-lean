import Proofs.Runtime.Caliper.BLSReplyPrepare

/-! Budgets for constructing the complete reply's cache request. All frame
copies and the stored fallback constant are charged by the executed program. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply

open Caliper BoundedSource

variable {w : Nat} {M R C G : Type} [DecidableEq M] (layout : Layouts w M R C G)
    (default : layout.cache.value.Value) (signing : Bool)

theorem message_bounded : (message layout default signing).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply ((Implementation.first_boundedBy layout.cache.key layout.store layout.cache.wordFits layout.plainInput.representation.fits).restrictInput
    (layout.guard default.val signing)).mono
  all_goals
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem store_bounded : (store layout default signing).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply ((Implementation.second_boundedBy layout.cache.key layout.store layout.cache.wordFits layout.plainInput.representation.fits).restrictInput
    (layout.guard default.val signing)).mono
  all_goals
    simp only [Layouts.store_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem config_bounded : (config layout default signing).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((store_bounded layout default signing).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem cacheLogs_bounded : (cacheLogs layout default signing).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((store_bounded layout default signing).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals
    simp only [Layouts.cacheLogs_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem oldCache_bounded : (oldCache layout default signing).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((cacheLogs_bounded layout default signing).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem logs_bounded : (logs layout default signing).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((cacheLogs_bounded layout default signing).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals
    simp only [Layouts.transcript_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem tableTail_bounded : (tableTail layout default signing).BoundedBy (112 * layout.width) (364 * layout.width + 182) := by
  have unitWords : (DataImplementation.unitLayout w).representation.encoding.words = 0 := rfl
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (oldCache_bounded layout default signing) (DataImplementation.unit_boundedBy _ _)).mono
  all_goals
    simp only [Layouts.input_words, Layouts.plainInput_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem valueTail_bounded : (valueTail layout default signing).BoundedBy (224 * layout.width) (728 * layout.width + 320) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (Implementation.constant_bounded _ _ _ _) (tableTail_bounded layout default signing)).mono
  all_goals
    simp only [Layouts.input_words, Layouts.plainInput_words, LookupLayout.tableTail_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem cacheArguments_bounded : (cacheArguments layout default signing).BoundedBy (336 * layout.width) (1092 * layout.width + 458) := by
  apply ((Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (message_bounded layout default signing) (valueTail_bounded layout default signing)).restrictOutput
    layout.cache.admissible (fun _ valid => valid.2.1)).mono
  all_goals
    simp only [Layouts.input_words, Layouts.plainInput_words, LookupLayout.valueTail_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem prepare_bounded : (prepare layout default signing).BoundedBy (440 * layout.width) (1430 * layout.width + 583) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (cacheArguments_bounded layout default signing) (Implementation.identity_boundedBy _ _)).mono
  all_goals
    simp only [Layouts.input_words, Layouts.plainInput_words, Layouts.cacheInput_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

end Signatures.Runtime.CaliperBackend.BLSReply
