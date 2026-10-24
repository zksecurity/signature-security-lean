import Proofs.Runtime.Caliper.ListFixedCons
import Proofs.Runtime.Caliper.PairBounds
import Proofs.Runtime.LazyAGMReply

/-! Bounded storage for the two explicit-reply logs. Both logs keep their
capacity during insertion; the selected log must have one unused entry slot. -/

namespace Signatures.Runtime.CaliperBackend.BLSRecord

open Caliper BoundedSource

abbrev Transcript (M G : Type) := Model.LazyAGM.Transcript M M G
abbrev Input (M G : Type) := (M × G) × Transcript M G

structure Layouts (w : Nat) (M G : Type) where
  message : Layout w M
  point : Layout w G
  capacityPred : Nat
  wordFits : 16 < 2 ^ w
  countFits : capacityPred + 1 < 2 ^ w
  storageFits : 8 * (message.representation.encoding.words + point.representation.encoding.words +
    2 * (1 + (capacityPred + 1) * (message.representation.encoding.words + point.representation.encoding.words))) < 2 ^ w

namespace Layouts

variable {w : Nat} {M G : Type} (layout : Layouts w M G)

def entryWords : Nat := layout.message.representation.encoding.words + layout.point.representation.encoding.words
def logWords : Nat := 1 + (layout.capacityPred + 1) * layout.entryWords
def width : Nat := layout.entryWords + 2 * layout.logWords

theorem fits_of_le {words : Nat} (bound : words ≤ 8 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def entry : Layout w (M × G) := layout.message.prod layout.point (layout.fits_of_le (by
  dsimp only [width, entryWords, logWords]; omega))

@[simp] theorem entry_words : layout.entry.representation.encoding.words = layout.entryWords := rfl

def log : Layout w (List (M × G)) := layout.entry.boundedList (layout.capacityPred + 1) layout.countFits
  (layout.fits_of_le (by change layout.logWords ≤ _; dsimp only [width]; omega))

@[simp] theorem log_words : layout.log.representation.encoding.words = layout.logWords := rfl

def transcript : Layout w (Transcript M G) := layout.log.prod layout.log (layout.fits_of_le (by
  rw [log_words]; dsimp only [width]; omega))

@[simp] theorem transcript_words : layout.transcript.representation.encoding.words = 2 * layout.logWords := by
  change layout.logWords + layout.logWords = _; omega

def unrestrictedInput : Layout w (Input M G) := layout.entry.prod layout.transcript (layout.fits_of_le (by
  rw [entry_words, transcript_words]; dsimp only [width]; omega))

@[simp] theorem unrestrictedInput_words : layout.unrestrictedInput.representation.encoding.words = layout.width := by
  change layout.entryWords + (layout.logWords + layout.logWords) = _; dsimp only [width]; omega

def room (signing : Bool) (value : Input M G) : Prop :=
  (if signing then value.2.2 else value.2.1).length ≤ layout.capacityPred

instance (signing : Bool) : DecidablePred (layout.room signing) := fun _ => inferInstanceAs (Decidable (_ ≤ _))

def input (signing : Bool) : Layout w (Input M G) := layout.unrestrictedInput.restrict (layout.room signing)

@[simp] theorem input_words (signing : Bool) : (layout.input signing).representation.encoding.words = layout.width :=
  layout.unrestrictedInput_words

theorem fixedConsFits : 1 + (layout.capacityPred + 2) * layout.entry.representation.encoding.words < 2 ^ w := by
  apply layout.fits_of_le
  rw [entry_words]
  dsimp only [width, logWords]
  nlinarith

def entryLog : Layout w ((M × G) × List (M × G)) := layout.entry.prod layout.log (layout.fits_of_le (by
  rw [entry_words, log_words]; dsimp only [width]; omega))

def output : Layout w (G × Transcript M G) := layout.point.prod layout.transcript (layout.fits_of_le (by
  rw [transcript_words]; dsimp only [width, entryWords]; omega))

include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (small : buffers ≤ 16) : body.program.savedBuffer < 2 ^ w := by
  have hw := layout.wordFits
  change max 2 body.program.code.memBound < 2 ^ w
  omega

end Layouts
end Signatures.Runtime.CaliperBackend.BLSRecord
