import Proofs.Runtime.Caliper.BLSCache
import Proofs.Runtime.Caliper.BLSRecordBounds
import Proofs.Runtime.Caliper.EncodedConstant

/-! Stored configurations and frames for the complete private BLS reply. The
cache and recorder share the message layout. Challenge points remain data. -/

namespace Signatures.Runtime.CaliperBackend.BLSReply

open Caliper BoundedSource

abbrev Store (M R C G : Type) := C × (List (M × R) × BLSRecord.Transcript M G)
abbrev Input (M R C G : Type) := M × Store M R C G
abbrev Post (M R C G : Type) := (R × List (M × R)) × Input M R C G
abbrev Frame (M R C G : Type) := G × Post M R C G

structure Layouts (w : Nat) (M R C G : Type) where
  cache : CacheLayout w M R
  point : Layout w G
  config : Layout w C
  capacityPred : Nat
  countFits : capacityPred + 1 < 2 ^ w
  storageFits : 16 * (cache.lookup.width + config.representation.encoding.words + point.representation.encoding.words +
    2 * (1 + (capacityPred + 1) * (cache.key.representation.encoding.words + point.representation.encoding.words))) < 2 ^ w

namespace Layouts

variable {w : Nat} {M R C G : Type} (layout : Layouts w M R C G)

def logWords : Nat := 1 + (layout.capacityPred + 1) * (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words)
def width : Nat := layout.cache.lookup.width + layout.config.representation.encoding.words + layout.point.representation.encoding.words + 2 * layout.logWords

theorem lookup_width : layout.cache.lookup.width = layout.cache.key.representation.encoding.words +
    layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words := by
  rw [LookupLayout.table_words]
  dsimp only [LookupLayout.width, CacheLayout.lookup]
  omega

theorem fits_of_le {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def records : BLSRecord.Layouts w M G where
  message := layout.cache.key
  point := layout.point
  capacityPred := layout.capacityPred
  wordFits := layout.cache.wordFits
  countFits := layout.countFits
  storageFits := layout.fits_of_le (by
    change 8 * (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words + 2 * layout.logWords) ≤ _
    dsimp only [width]; rw [lookup_width]; omega)

@[simp] theorem transcript_words : layout.records.transcript.representation.encoding.words = 2 * layout.logWords :=
  layout.records.transcript_words

def cacheLogs : Layout w (List (M × R) × BLSRecord.Transcript M G) :=
  layout.cache.lookup.table.prod layout.records.transcript (layout.fits_of_le (by
    rw [transcript_words]; dsimp only [width]; rw [lookup_width]; omega))

def store : Layout w (Store M R C G) := layout.config.prod layout.cacheLogs (layout.fits_of_le (by
  change _ + (_ + _) ≤ _
  rw [transcript_words]; dsimp only [width]; rw [lookup_width]; omega))

def plainInput : Layout w (Input M R C G) := layout.cache.key.prod layout.store (layout.fits_of_le (by
  change _ + (_ + (_ + _)) ≤ _
  rw [transcript_words]; dsimp only [width]; rw [lookup_width]; omega))

def responseInput : Layout w (R × C) := layout.cache.value.prod layout.config (layout.fits_of_le (by
  dsimp only [width]; rw [lookup_width]; omega))

def output : Layout w (G × Store M R C G) := layout.point.prod layout.store (layout.fits_of_le (by
  change _ + (_ + (_ + _)) ≤ _
  rw [transcript_words]; dsimp only [width]; rw [lookup_width]; omega))

@[simp] theorem cacheLogs_words : layout.cacheLogs.representation.encoding.words =
    layout.cache.lookup.table.representation.encoding.words + 2 * layout.logWords := by
  change _ + _ = _; rw [transcript_words]
@[simp] theorem store_words : layout.store.representation.encoding.words =
    layout.config.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words + 2 * layout.logWords := by
  change _ + layout.cacheLogs.representation.encoding.words = _; rw [cacheLogs_words]; omega
@[simp] theorem plainInput_words : layout.plainInput.representation.encoding.words =
    layout.cache.key.representation.encoding.words + layout.config.representation.encoding.words +
      layout.cache.lookup.table.representation.encoding.words + 2 * layout.logWords := by
  change _ + layout.store.representation.encoding.words = _; rw [store_words]; omega

@[simp] theorem cacheInput_words [DecidableEq M] : layout.cache.input.representation.encoding.words = layout.cache.lookup.width :=
  layout.cache.lookup.input_words

@[simp] theorem cacheOutput_words : (CacheRead.output layout.cache).representation.encoding.words =
    layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words := rfl


variable [DecidableEq M]

def guard (default : R) (signing : Bool) (value : Input M R C G) : Prop :=
  layout.cache.admissible (value.1, default, value.2.2.1, ()) ∧
    (if signing then value.2.2.2.2 else value.2.2.2.1).length ≤ layout.capacityPred

instance (default : R) (signing : Bool) : DecidablePred (layout.guard default signing) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

def input (default : R) (signing : Bool) : Layout w (Input M R C G) := layout.plainInput.restrict (layout.guard default signing)

@[simp] theorem input_words (default : R) (signing : Bool) :
    (layout.input default signing).representation.encoding.words = layout.plainInput.representation.encoding.words := rfl

def prepared (default : R) (signing : Bool) : Layout w (CacheLayout.Input M R × Input M R C G) :=
  layout.cache.input.prod (layout.input default signing) (layout.fits_of_le (by
    change layout.cache.lookup.input.representation.encoding.words + (layout.input default signing).representation.encoding.words ≤ _
    rw [LookupLayout.input_words, input_words, plainInput_words]; dsimp only [width]; rw [lookup_width]; omega))

def post (default : R) (signing : Bool) : Layout w (Post M R C G) :=
  (CacheRead.output layout.cache).prod (layout.input default signing) (layout.fits_of_le (by
    change (layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words) + _ ≤ _
    rw [input_words, plainInput_words]; dsimp only [width]; rw [lookup_width]; omega))

def frame (default : R) (signing : Bool) : Layout w (Frame M R C G) :=
  layout.point.prod (layout.post default signing) (layout.fits_of_le (by
    change _ + ((_ + _) + (layout.input default signing).representation.encoding.words) ≤ _
    rw [input_words, plainInput_words]; dsimp only [width]; rw [lookup_width]; omega))

@[simp] theorem post_words (default : R) (signing : Bool) : (layout.post default signing).representation.encoding.words =
    layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words +
      layout.plainInput.representation.encoding.words := rfl
@[simp] theorem frame_words (default : R) (signing : Bool) : (layout.frame default signing).representation.encoding.words =
    layout.point.representation.encoding.words + (layout.post default signing).representation.encoding.words := rfl

theorem input_le (default : R) (signing : Bool) : (layout.input default signing).representation.encoding.words ≤ layout.width := by
  rw [input_words, plainInput_words]; dsimp only [width]; rw [lookup_width]; omega

theorem post_le (default : R) (signing : Bool) : (layout.post default signing).representation.encoding.words ≤ 2 * layout.width := by
  rw [post_words, plainInput_words]; dsimp only [width]; rw [lookup_width]; omega

theorem frame_le (default : R) (signing : Bool) : (layout.frame default signing).representation.encoding.words ≤ 2 * layout.width := by
  rw [frame_words, post_words, plainInput_words]; dsimp only [width]; rw [lookup_width]; omega

include layout in
omit [DecidableEq M] in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (fits : buffers < 2 ^ w) : body.program.savedBuffer < 2 ^ w := by
  have hw := layout.cache.wordFits
  change max 2 body.program.code.memBound < 2 ^ w
  omega

include layout in
omit [DecidableEq M] in
theorem smallNameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (small : buffers ≤ 16) : body.program.savedBuffer < 2 ^ w :=
  layout.nameFits body bound (small.trans_lt layout.cache.wordFits)

end Layouts
end Signatures.Runtime.CaliperBackend.BLSReply
