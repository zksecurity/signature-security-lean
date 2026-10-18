import Signatures.Runtime.Caliper.BLSReplyFinish
import Signatures.Runtime.Caliper.BLSReplyPrepareBounds

/-! Derived budgets for response wiring and recording. Only the supplied
arithmetic response contributes a primitive budget; every copy is charged. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply

open Caliper BoundedSource

variable {w : Nat} {M R C G : Type} [DecidableEq M] (layout : Layouts w M R C G)
    (default : layout.cache.value.Value) (signing : Bool)

theorem postOriginal_bounded : (postOriginal layout default signing).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.second_boundedBy _ _ _ _).mono
  all_goals
    simp only [Layouts.input_words, Layouts.plainInput_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem sample_bounded : (sample layout default signing).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.first_boundedBy _ _ _ _).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals
    simp only [Layout.prod_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem postConfig_bounded : (postConfig layout default signing).BoundedBy (24 * layout.width) (78 * layout.width + 44) := by
  apply ((postOriginal_bounded layout default signing).then (config_bounded layout default signing)).mono
  all_goals
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem framePost_bounded : (framePost layout default signing).BoundedBy (16 * layout.width) (52 * layout.width + 14) := by
  apply (Implementation.second_boundedBy _ _ _ _).mono
  all_goals
    simp only [Layouts.post_words, Layouts.plainInput_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem frameOriginal_bounded : (frameOriginal layout default signing).BoundedBy (24 * layout.width) (78 * layout.width + 29) := by
  apply ((framePost_bounded layout default signing).then (postOriginal_bounded layout default signing)).mono
  all_goals
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem frameMessage_bounded : (frameMessage layout default signing).BoundedBy (32 * layout.width) (104 * layout.width + 44) := by
  apply ((frameOriginal_bounded layout default signing).then (message_bounded layout default signing)).mono
  all_goals
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem frameConfig_bounded : (frameConfig layout default signing).BoundedBy (40 * layout.width) (130 * layout.width + 59) := by
  apply ((frameOriginal_bounded layout default signing).then (config_bounded layout default signing)).mono
  all_goals
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem frameLogs_bounded : (frameLogs layout default signing).BoundedBy (48 * layout.width) (156 * layout.width + 74) := by
  apply ((frameOriginal_bounded layout default signing).then (logs_bounded layout default signing)).mono
  all_goals
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem newCache_bounded : (newCache layout default signing).BoundedBy (32 * layout.width) (104 * layout.width + 44) := by
  apply (((framePost_bounded layout default signing).then (Implementation.first_boundedBy _ _ _ _)).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals
    simp only [Layouts.cacheOutput_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem framePoint_bounded : (framePoint layout default signing).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.first_boundedBy _ _ _ _).mono
  all_goals
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem event_bounded : (event layout default signing).BoundedBy (196 * layout.width) (637 * layout.width + 182) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (frameMessage_bounded layout default signing) (framePoint_bounded layout default signing)).mono
  all_goals
    simp only [Layouts.frame_words, Layouts.post_words, Layouts.plainInput_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem recordArguments_bounded : (recordArguments layout default signing).BoundedBy (400 * layout.width) (1300 * layout.width + 380) := by
  apply ((Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (event_bounded layout default signing) (frameLogs_bounded layout default signing)).restrictOutput (layout.records.room signing) (fun _ valid => valid.2.2.2.2)).mono
  all_goals
    simp only [Layouts.frame_words, Layouts.post_words, Layouts.plainInput_words, BLSRecord.Layouts.entry_words, Layouts.transcript_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup, BLSRecord.Layouts.entryWords, Layouts.records]
    omega

theorem responseArguments_bounded : (responseArguments layout default signing).BoundedBy (196 * layout.width) (637 * layout.width + 197) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (sample_bounded layout default signing) (postConfig_bounded layout default signing)).mono
  all_goals
    simp only [Layouts.post_words, Layouts.plainInput_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem recorded_bounded : (recorded layout default signing).BoundedBy
    (888 * layout.width + 5) (2886 * layout.width + 755) := by
  apply ((recordArguments_bounded layout default signing).then (BLSRecord.record_bounded layout.records signing)).mono
  all_goals
    dsimp only [BLSRecord.recordTime, BLSRecord.recordWords, BLSRecord.Layouts.entryWords, BLSRecord.Layouts.logWords, Layouts.records, Layouts.width, Layouts.logWords]
    rw [Layouts.lookup_width]
    omega

theorem newCacheLogs_bounded : (newCacheLogs layout default signing).BoundedBy (1076 * layout.width + 5) (3497 * layout.width + 923) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (newCache_bounded layout default signing) (recorded_bounded layout default signing)).mono
  all_goals
    simp only [Layouts.frame_words, Layouts.post_words, Layouts.plainInput_words, Layouts.transcript_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem newStore_bounded : (newStore layout default signing).BoundedBy (1272 * layout.width + 5) (4134 * layout.width + 1106) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (frameConfig_bounded layout default signing) (newCacheLogs_bounded layout default signing)).mono
  all_goals
    simp only [Layouts.frame_words, Layouts.post_words, Layouts.plainInput_words, Layouts.cacheLogs_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

theorem result_bounded : (result layout default signing).BoundedBy (1436 * layout.width + 5) (4667 * layout.width + 1244) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (framePoint_bounded layout default signing) (newStore_bounded layout default signing)).mono
  all_goals
    simp only [Layouts.frame_words, Layouts.post_words, Layouts.plainInput_words, Layouts.store_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    dsimp only [CacheLayout.lookup]
    omega

variable {respond : R × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {slots : Nat} (responseBuffers : response.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)
    {responseTime responseWords : Nat} (responseBound : response.BoundedBy responseTime responseWords)

include responseBound in
theorem responseOnPost_bounded : (responseOnPost layout default signing response).BoundedBy
    (responseTime + 196 * layout.width) (responseWords + 637 * layout.width + 198) := by
  apply ((responseArguments_bounded layout default signing).then responseBound).mono <;> omega

include responseBound in
theorem withResponse_bounded : (withResponse layout default signing response responseBuffers reserve).BoundedBy
    (responseTime + 368 * layout.width) (responseWords + 1196 * layout.width + 323) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (responseOnPost_bounded layout default signing response responseBound)
    (Implementation.identity_boundedBy _ _)).mono
  all_goals
    simp only [Layouts.post_words, Layouts.plainInput_words]
    dsimp only [Layouts.width]
    rw [Layouts.lookup_width]
    omega

include responseBound in
theorem finish_bounded : (finish layout default signing response responseBuffers reserve).BoundedBy
    (responseTime + 1804 * layout.width + 5) (responseWords + 5863 * layout.width + 1568) := by
  apply ((withResponse_bounded layout default signing response responseBuffers reserve responseBound).then
    (result_bounded layout default signing)).mono <;> omega

end Signatures.Runtime.CaliperBackend.BLSReply
