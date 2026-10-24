import Proofs.Runtime.Caliper.BLSReplyLayout

/-! Build the private cache request and save the full original reply frame by
executed copies. The fallback constant and empty environment are actual code. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply

open Caliper BoundedSource

variable {w : Nat} {M R C G : Type} [DecidableEq M] (layout : Layouts w M R C G)
    (default : layout.cache.value.Value) (signing : Bool)

def message : Implementation .unit (layout.input default.val signing) layout.cache.key Prod.fst :=
  (Implementation.first (by decide) layout.cache.key layout.store layout.cache.wordFits _).restrictInput (layout.guard default.val signing)

def store : Implementation .unit (layout.input default.val signing) layout.store Prod.snd :=
  (Implementation.second (by decide) layout.cache.key layout.store layout.cache.wordFits _).restrictInput (layout.guard default.val signing)

def config : Implementation .unit (layout.input default.val signing) layout.config (fun value => value.2.1) :=
  (store layout default signing).then (Implementation.first (by decide) layout.config layout.cacheLogs layout.cache.wordFits _)

def cacheLogs : Implementation .unit (layout.input default.val signing) layout.cacheLogs (fun value => value.2.2) :=
  (store layout default signing).then (Implementation.second (by decide) layout.config layout.cacheLogs layout.cache.wordFits _)

def oldCache : Implementation .unit (layout.input default.val signing) layout.cache.lookup.table (fun value => value.2.2.1) :=
  (cacheLogs layout default signing).then (Implementation.first (by decide) layout.cache.lookup.table layout.records.transcript layout.cache.wordFits _)

def logs : Implementation .unit (layout.input default.val signing) layout.records.transcript (fun value => value.2.2.2) :=
  (cacheLogs layout default signing).then (Implementation.second (by decide) layout.cache.lookup.table layout.records.transcript layout.cache.wordFits _)

theorem message_buffers : (message layout default signing).program.code.memBound ≤ 2 :=
  Implementation.first_buffers (cost := .unit) (by decide) layout.cache.key layout.store layout.cache.wordFits layout.plainInput.representation.fits
theorem store_buffers : (store layout default signing).program.code.memBound ≤ 2 :=
  Implementation.second_buffers (cost := .unit) (by decide) layout.cache.key layout.store layout.cache.wordFits layout.plainInput.representation.fits
theorem config_buffers : (config layout default signing).program.code.memBound ≤ 2 :=
  max_le (store_buffers layout default signing) (Implementation.first_buffers _ _ _ _ _)
theorem cacheLogs_buffers : (cacheLogs layout default signing).program.code.memBound ≤ 2 :=
  max_le (store_buffers layout default signing) (Implementation.second_buffers _ _ _ _ _)
theorem oldCache_buffers : (oldCache layout default signing).program.code.memBound ≤ 2 :=
  max_le (cacheLogs_buffers layout default signing) (Implementation.first_buffers _ _ _ _ _)
theorem logs_buffers : (logs layout default signing).program.code.memBound ≤ 2 :=
  max_le (cacheLogs_buffers layout default signing) (Implementation.second_buffers _ _ _ _ _)

def tableTail : Implementation .unit (layout.input default.val signing) layout.cache.lookup.tableTail
    (fun value => (value.2.2.1, ())) :=
  (oldCache layout default signing).pair (DataImplementation.unit .unit (by decide) _ layout.cache.wordFits)
    (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (oldCache_buffers layout default signing) (by decide))
    (by change 2 < 2 ^ w; have h := layout.cache.wordFits; omega)
    (layout.fits_of_le (by have h := layout.input_le default.val signing; omega))
    (layout.fits_of_le (by have h := layout.input_le default.val signing; dsimp only [Layouts.width] at h ⊢; rw [Layouts.lookup_width] at h ⊢; omega)) _

theorem tableTail_buffers : (tableTail layout default signing).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (oldCache_buffers layout default signing) (show _ ≤ 2 from le_rfl)

def valueTail : Implementation .unit (layout.input default.val signing) layout.cache.lookup.valueTail
    (fun value => (default.val, value.2.2.1, ())) :=
  (Implementation.constant (layout.input default.val signing) layout.cache.value default layout.cache.wordFits).pair
    (tableTail layout default signing) (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (Implementation.constant_buffers _ _ _ _) (by decide))
    (layout.smallNameFits _ (tableTail_buffers layout default signing) (by decide))
    (layout.fits_of_le (by have h := layout.input_le default.val signing; omega))
    (layout.fits_of_le (by have h := layout.input_le default.val signing; dsimp only [Layouts.width] at h ⊢; rw [Layouts.lookup_width] at h ⊢; omega)) _

theorem valueTail_buffers : (valueTail layout default signing).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (Implementation.constant_buffers _ _ _ _) (tableTail_buffers layout default signing)

def cacheArguments : Implementation .unit (layout.input default.val signing) layout.cache.input
    (fun value => (value.1, default.val, value.2.2.1, ())) :=
  ((message layout default signing).pair (valueTail layout default signing) (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (message_buffers layout default signing) (by decide))
    (layout.smallNameFits _ (valueTail_buffers layout default signing) (by decide))
    (layout.fits_of_le (by have h := layout.input_le default.val signing; omega))
    (layout.fits_of_le (by have h := layout.input_le default.val signing; dsimp only [Layouts.width] at h ⊢; rw [Layouts.lookup_width] at h ⊢; omega)) _).restrictOutput
      layout.cache.admissible (fun _ valid => valid.2.1)

theorem cacheArguments_buffers : (cacheArguments layout default signing).program.code.memBound ≤ 5 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ layout.cache.lookup.input.representation.fits (message_buffers layout default signing) (valueTail_buffers layout default signing)

def prepare : Implementation .unit (layout.input default.val signing) (layout.prepared default.val signing)
    (fun value => ((value.1, default.val, value.2.2.1, ()), value)) :=
  (cacheArguments layout default signing).pair (Implementation.identity _ (width_pos layout.cache.wordFits))
    (by decide) layout.cache.wordFits
    (layout.smallNameFits _ (cacheArguments_buffers layout default signing) (by decide))
    (by change 2 < 2 ^ w; have h := layout.cache.wordFits; omega)
    (layout.fits_of_le (by have h := layout.input_le default.val signing; omega))
    (layout.prepared default.val signing).representation.fits _

theorem prepare_buffers : (prepare layout default signing).program.code.memBound ≤ 6 :=
  Implementation.pair_buffers _ _ _ _ _ _ _ _ (cacheArguments_buffers layout default signing) (show _ ≤ 0 from le_rfl)

end Signatures.Runtime.CaliperBackend.BLSReply
