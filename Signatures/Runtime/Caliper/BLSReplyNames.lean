import Signatures.Runtime.Caliper.BLSReplyFinish
import Signatures.Runtime.Caliper.CacheReadMemory

/-! Generated name accounting for the reply's pure frame construction and
response path. Only the arithmetic primitive contributes reserved names. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply

open Caliper BoundedSource

variable {w : Nat} {M R C G : Type} [DecidableEq M] (layout : Layouts w M R C G)
    (default : layout.cache.value.Value) (signing : Bool) (names : Nat)

theorem message_names : NamesAccounted (message layout default signing).program.code names :=
  Implementation.first_names layout.cache.key layout.store layout.cache.wordFits layout.plainInput.representation.fits names

theorem store_names : NamesAccounted (store layout default signing).program.code names :=
  Implementation.second_names layout.cache.key layout.store layout.cache.wordFits layout.plainInput.representation.fits names

theorem config_names : NamesAccounted (config layout default signing).program.code names :=
  (store_names layout default signing names).seq (Implementation.first_names _ _ _ _ _)

theorem cacheLogs_names : NamesAccounted (cacheLogs layout default signing).program.code names :=
  (store_names layout default signing names).seq (Implementation.second_names _ _ _ _ _)

theorem oldCache_names : NamesAccounted (oldCache layout default signing).program.code names :=
  (cacheLogs_names layout default signing names).seq (Implementation.first_names _ _ _ _ _)

theorem logs_names : NamesAccounted (logs layout default signing).program.code names :=
  (cacheLogs_names layout default signing names).seq (Implementation.second_names _ _ _ _ _)

theorem tableTail_names : NamesAccounted (tableTail layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (oldCache_names layout default signing names) (DataImplementation.unit_names _ _ _)

theorem valueTail_names : NamesAccounted (valueTail layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (Implementation.constant_names _ _ _ _ _) (tableTail_names layout default signing names)

theorem cacheArguments_names : NamesAccounted (cacheArguments layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ layout.cache.lookup.input.representation.fits
    (message_names layout default signing names) (valueTail_names layout default signing names)

theorem prepare_names : NamesAccounted (prepare layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (cacheArguments_names layout default signing names) (skip_names names)

theorem postOriginal_names : NamesAccounted (postOriginal layout default signing).program.code names :=
  Implementation.second_names _ _ _ _ _

theorem sample_names : NamesAccounted (sample layout default signing).program.code names :=
  (Implementation.first_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _)

theorem postConfig_names : NamesAccounted (postConfig layout default signing).program.code names :=
  (postOriginal_names layout default signing names).seq (config_names layout default signing names)

theorem framePost_names : NamesAccounted (framePost layout default signing).program.code names :=
  Implementation.second_names _ _ _ _ _

theorem frameOriginal_names : NamesAccounted (frameOriginal layout default signing).program.code names :=
  (framePost_names layout default signing names).seq (postOriginal_names layout default signing names)

theorem frameMessage_names : NamesAccounted (frameMessage layout default signing).program.code names :=
  (frameOriginal_names layout default signing names).seq (message_names layout default signing names)

theorem frameConfig_names : NamesAccounted (frameConfig layout default signing).program.code names :=
  (frameOriginal_names layout default signing names).seq (config_names layout default signing names)

theorem frameLogs_names : NamesAccounted (frameLogs layout default signing).program.code names :=
  (frameOriginal_names layout default signing names).seq (logs_names layout default signing names)

theorem newCache_names : NamesAccounted (newCache layout default signing).program.code names :=
  ((framePost_names layout default signing names).seq (Implementation.first_names _ _ _ _ _)).seq (Implementation.second_names _ _ _ _ _)

theorem framePoint_names : NamesAccounted (framePoint layout default signing).program.code names :=
  Implementation.first_names _ _ _ _ _

theorem event_names : NamesAccounted (event layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (frameMessage_names layout default signing names) (framePoint_names layout default signing names)

theorem recordArguments_names : NamesAccounted (recordArguments layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ layout.records.unrestrictedInput.representation.fits (event_names layout default signing names) (frameLogs_names layout default signing names)

theorem recorded_names : NamesAccounted (recorded layout default signing).program.code names :=
  (recordArguments_names layout default signing names).seq (BLSRecord.record_names layout.records names signing)

theorem newCacheLogs_names : NamesAccounted (newCacheLogs layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (newCache_names layout default signing names) (recorded_names layout default signing names)

theorem newStore_names : NamesAccounted (newStore layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (frameConfig_names layout default signing names) (newCacheLogs_names layout default signing names)

theorem result_names : NamesAccounted (result layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (framePoint_names layout default signing names) (newStore_names layout default signing names)

theorem responseArguments_names : NamesAccounted (responseArguments layout default signing).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (sample_names layout default signing names) (postConfig_names layout default signing names)

variable {respond : R × C → G} (response : Implementation .unit layout.responseInput layout.point respond)
    {slots : Nat} (responseBuffers : response.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)
    (responseNames : NamesAccounted response.program.code names)

include responseNames in
theorem responseOnPost_names : NamesAccounted (responseOnPost layout default signing response).program.code names :=
  (responseArguments_names layout default signing names).seq responseNames

include responseNames in
theorem withResponse_names : NamesAccounted (withResponse layout default signing response responseBuffers reserve).program.code names :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (responseOnPost_names layout default signing names response responseNames) (skip_names names)

include responseNames in
theorem finish_names : NamesAccounted (finish layout default signing response responseBuffers reserve).program.code names :=
  (withResponse_names layout default signing names response responseBuffers reserve responseNames).seq (result_names layout default signing names)

theorem withResponse_buffers : (withResponse layout default signing response responseBuffers reserve).program.code.memBound ≤ max 3 slots + 1 := by
  apply (Implementation.pair_buffers _ _ _ _ _ _ _ _ (responseOnPost_buffers layout default signing response responseBuffers)
    (show (Implementation.identity (cost := .unit) (layout.post default.val signing) (width_pos layout.cache.wordFits)).program.code.memBound ≤ 0 from le_rfl)).trans
  omega

theorem finish_buffers : (finish layout default signing response responseBuffers reserve).program.code.memBound ≤ max 7 (slots + 1) := by
  have left := withResponse_buffers layout default signing response responseBuffers reserve
  have right := result_buffers layout default signing
  change max _ _ ≤ _
  omega

end Signatures.Runtime.CaliperBackend.BLSReply
