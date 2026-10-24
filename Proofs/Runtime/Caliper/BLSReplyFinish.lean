import Proofs.Runtime.Caliper.BLSReplyPrepare

/-! After the cache call, calculate the response once, record that stored point,
and return the updated store. All surrounding routing is generated Caliper code. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply

open Caliper BoundedSource

variable {w : Nat} {M R C G : Type} [DecidableEq M] (layout : Layouts w M R C G)
    (default : layout.cache.value.Value) (signing : Bool)

def postOriginal : Implementation .unit (layout.post default.val signing) (layout.input default.val signing) Prod.snd :=
  Implementation.second (by decide) (CacheRead.output layout.cache) (layout.input default.val signing) layout.cache.wordFits _

def sample : Implementation .unit (layout.post default.val signing) layout.cache.value (fun value => value.1.1) :=
  (Implementation.first (by decide) (CacheRead.output layout.cache) (layout.input default.val signing) layout.cache.wordFits _).then
    (Implementation.first (by decide) layout.cache.value layout.cache.lookup.table layout.cache.wordFits _)

def postConfig : Implementation .unit (layout.post default.val signing) layout.config (fun value => value.2.2.1) :=
  (postOriginal layout default signing).then (config layout default signing)

def framePost : Implementation .unit (layout.frame default.val signing) (layout.post default.val signing) Prod.snd :=
  Implementation.second (by decide) layout.point (layout.post default.val signing) layout.cache.wordFits _

def frameOriginal : Implementation .unit (layout.frame default.val signing) (layout.input default.val signing) (fun value => value.2.2) :=
  (framePost layout default signing).then (postOriginal layout default signing)

def frameMessage : Implementation .unit (layout.frame default.val signing) layout.cache.key (fun value => value.2.2.1) :=
  (frameOriginal layout default signing).then (message layout default signing)

def frameConfig : Implementation .unit (layout.frame default.val signing) layout.config (fun value => value.2.2.2.1) :=
  (frameOriginal layout default signing).then (config layout default signing)

def frameLogs : Implementation .unit (layout.frame default.val signing) layout.records.transcript (fun value => value.2.2.2.2.2) :=
  (frameOriginal layout default signing).then (logs layout default signing)

def newCache : Implementation .unit (layout.frame default.val signing) layout.cache.lookup.table (fun value => value.2.1.2) :=
  ((framePost layout default signing).then
    (Implementation.first (by decide) (CacheRead.output layout.cache) (layout.input default.val signing) layout.cache.wordFits _)).then
      (Implementation.second (by decide) layout.cache.value layout.cache.lookup.table layout.cache.wordFits _)

def framePoint : Implementation .unit (layout.frame default.val signing) layout.point Prod.fst :=
  Implementation.first (by decide) layout.point (layout.post default.val signing) layout.cache.wordFits _

theorem postOriginal_buffers : (postOriginal layout default signing).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem sample_buffers : (sample layout default signing).program.code.memBound ≤ 2 :=
  max_le (Implementation.first_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem postConfig_buffers : (postConfig layout default signing).program.code.memBound ≤ 2 :=
  max_le (postOriginal_buffers layout default signing) (config_buffers layout default signing)
theorem framePost_buffers : (framePost layout default signing).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem frameOriginal_buffers : (frameOriginal layout default signing).program.code.memBound ≤ 2 :=
  max_le (framePost_buffers layout default signing) (postOriginal_buffers layout default signing)
theorem frameMessage_buffers : (frameMessage layout default signing).program.code.memBound ≤ 2 :=
  max_le (frameOriginal_buffers layout default signing) (message_buffers layout default signing)
theorem frameConfig_buffers : (frameConfig layout default signing).program.code.memBound ≤ 2 :=
  max_le (frameOriginal_buffers layout default signing) (config_buffers layout default signing)
theorem frameLogs_buffers : (frameLogs layout default signing).program.code.memBound ≤ 2 :=
  max_le (frameOriginal_buffers layout default signing) (logs_buffers layout default signing)
theorem newCache_buffers : (newCache layout default signing).program.code.memBound ≤ 2 :=
  max_le (max_le (framePost_buffers layout default signing) (Implementation.first_buffers _ _ _ _ _)) (Implementation.second_buffers _ _ _ _ _)
theorem framePoint_buffers : (framePoint layout default signing).program.code.memBound ≤ 2 :=
  Implementation.first_buffers (cost := .unit) (by decide) layout.point (layout.post default.val signing) layout.cache.wordFits
    (layout.frame default.val signing).representation.fits

def event : Implementation .unit (layout.frame default.val signing) layout.records.entry (fun value => (value.2.2.1, value.1)) :=
  (frameMessage layout default signing).pair (framePoint layout default signing) (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (frameMessage_buffers layout default signing) (by decide))
    (layout.smallNameFits _ (framePoint_buffers layout default signing) (by decide))
    (layout.fits_of_le (by have h := layout.frame_le default.val signing; omega))
    (layout.fits_of_le (by have h := layout.frame_le default.val signing; dsimp only [Layouts.width] at h ⊢; rw [Layouts.lookup_width] at h ⊢; omega)) _

theorem event_buffers : (event layout default signing).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (frameMessage_buffers layout default signing) (framePoint_buffers layout default signing)

def recordArguments : Implementation .unit (layout.frame default.val signing) (layout.records.input signing)
    (fun value => ((value.2.2.1, value.1), value.2.2.2.2.2)) :=
  ((event layout default signing).pair (frameLogs layout default signing) (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (event_buffers layout default signing) (by decide))
    (layout.smallNameFits _ (frameLogs_buffers layout default signing) (by decide))
    (layout.fits_of_le (by have h := layout.frame_le default.val signing; omega))
    (layout.fits_of_le (by
      change (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words) + _ ≤ _
      have h := layout.frame_le default.val signing; dsimp only [Layouts.width] at h ⊢; rw [Layouts.lookup_width] at h ⊢; omega)) _).restrictOutput
        (layout.records.room signing) (fun _ valid => valid.2.2.2.2)

theorem recordArguments_buffers : (recordArguments layout default signing).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ layout.records.unrestrictedInput.representation.fits
    (event_buffers layout default signing) (frameLogs_buffers layout default signing)

def recorded : Implementation .unit (layout.frame default.val signing) layout.records.transcript
    (fun value => LazyAGM.record signing value.2.2.1 value.1 value.2.2.2.2.2) :=
  (recordArguments layout default signing).then (BLSRecord.record layout.records signing)

theorem recorded_buffers : (recorded layout default signing).program.code.memBound ≤ 4 :=
  max_le (recordArguments_buffers layout default signing) (BLSRecord.record_buffers layout.records signing)

def newCacheLogs : Implementation .unit (layout.frame default.val signing) layout.cacheLogs
    (fun value => (value.2.1.2, LazyAGM.record signing value.2.2.1 value.1 value.2.2.2.2.2)) :=
  (newCache layout default signing).pair (recorded layout default signing) (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (newCache_buffers layout default signing) (by decide))
    (layout.smallNameFits _ (recorded_buffers layout default signing) (by decide))
    (layout.fits_of_le (by have h := layout.frame_le default.val signing; omega))
    (layout.fits_of_le (by have h := layout.frame_le default.val signing; dsimp only [Layouts.width] at h ⊢; rw [Layouts.lookup_width] at h ⊢; omega)) _

theorem newCacheLogs_buffers : (newCacheLogs layout default signing).program.code.memBound ≤ 5 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (newCache_buffers layout default signing) (recorded_buffers layout default signing)

def newStore : Implementation .unit (layout.frame default.val signing) layout.store
    (fun value => (value.2.2.2.1, value.2.1.2, LazyAGM.record signing value.2.2.1 value.1 value.2.2.2.2.2)) :=
  (frameConfig layout default signing).pair (newCacheLogs layout default signing) (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (frameConfig_buffers layout default signing) (by decide))
    (layout.smallNameFits _ (newCacheLogs_buffers layout default signing) (by decide))
    (layout.fits_of_le (by have h := layout.frame_le default.val signing; omega))
    (layout.fits_of_le (by have h := layout.frame_le default.val signing; dsimp only [Layouts.width] at h ⊢; rw [Layouts.lookup_width] at h ⊢; omega)) _

theorem newStore_buffers : (newStore layout default signing).program.code.memBound ≤ 6 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (frameConfig_buffers layout default signing) (newCacheLogs_buffers layout default signing)

def result : Implementation .unit (layout.frame default.val signing) layout.output
    (fun value => (value.1, value.2.2.2.1, value.2.1.2, LazyAGM.record signing value.2.2.1 value.1 value.2.2.2.2.2)) :=
  (framePoint layout default signing).pair (newStore layout default signing) (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (framePoint_buffers layout default signing) (by decide))
    (layout.smallNameFits _ (newStore_buffers layout default signing) (by decide))
    (layout.fits_of_le (by have h := layout.frame_le default.val signing; omega))
    (layout.fits_of_le (by have h := layout.frame_le default.val signing; dsimp only [Layouts.width] at h ⊢; rw [Layouts.lookup_width] at h ⊢; omega)) _

theorem result_buffers : (result layout default signing).program.code.memBound ≤ 7 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (framePoint_buffers layout default signing) (newStore_buffers layout default signing)

def responseArguments : Implementation .unit (layout.post default.val signing) layout.responseInput
    (fun value => (value.1.1, value.2.2.1)) :=
  (sample layout default signing).pair (postConfig layout default signing) (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (sample_buffers layout default signing) (by decide))
    (layout.smallNameFits _ (postConfig_buffers layout default signing) (by decide))
    (layout.fits_of_le (by have h := layout.post_le default.val signing; omega))
    (layout.fits_of_le (by have h := layout.post_le default.val signing; dsimp only [Layouts.width] at h ⊢; rw [Layouts.lookup_width] at h ⊢; omega)) _

theorem responseArguments_buffers : (responseArguments layout default signing).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (sample_buffers layout default signing) (postConfig_buffers layout default signing)

variable {respond : R × C → G} (response : Implementation .unit layout.responseInput layout.point respond)

def responseOnPost : Implementation .unit (layout.post default.val signing) layout.point (fun value => respond (value.1.1, value.2.2.1)) :=
  (responseArguments layout default signing).then response

variable {slots : Nat} (responseBuffers : response.program.code.memBound ≤ slots) (reserve : slots + 3 < 2 ^ w)

include responseBuffers in
theorem responseOnPost_buffers : (responseOnPost layout default signing response).program.code.memBound ≤ max 3 slots :=
  max_le ((responseArguments_buffers layout default signing).trans (Nat.le_max_left _ _)) (responseBuffers.trans (Nat.le_max_right _ _))

def withResponse : Implementation .unit (layout.post default.val signing) (layout.frame default.val signing)
    (fun value => (respond (value.1.1, value.2.2.1), value)) :=
  (responseOnPost layout default signing response).pair (Implementation.identity _ (width_pos layout.cache.wordFits))
    (by decide) layout.cache.wordFits
    (layout.nameFits _ (responseOnPost_buffers layout default signing response responseBuffers) (by have h := layout.cache.wordFits; omega))
    (by change 2 < 2 ^ w; have h := layout.cache.wordFits; omega)
    (layout.fits_of_le (by have h := layout.post_le default.val signing; omega))
    (layout.frame default.val signing).representation.fits _

def finishValue (respond : R × C → G) (signing : Bool) (value : Post M R C G) : G × Store M R C G :=
  let reply := respond (value.1.1, value.2.2.1)
  (reply, value.2.2.1, value.1.2, LazyAGM.record signing value.2.1 reply value.2.2.2.2)

def finish : Implementation .unit (layout.post default.val signing) layout.output (finishValue respond signing) :=
  (withResponse layout default signing response responseBuffers reserve).then (result layout default signing)

end Signatures.Runtime.CaliperBackend.BLSReply
