import Signatures.Runtime.Caliper.SchnorrROMTapeReplyBounds
import Signatures.Runtime.Caliper.ConstructedLiteral

/-! Executed caller request preparation and reply routing. Private requests
construct their original family tag and retain the requested range. Challenge
requests construct tag one. Every fallback cell and retained copy is charged. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def privateInput := (Reply.range layout).prod (Read.store layout) (layout.fits_of_le (by
  change 1 + (Read.store layout).representation.encoding.words ≤ _
  have := Read.store_le layout
  unfold Layouts.width at *
  omega))
theorem privateInput_le : (privateInput layout).representation.encoding.words ≤ 3 * layout.width := by
  change 1 + (Read.store layout).representation.encoding.words ≤ _
  have := Read.store_le layout
  unfold Layouts.width at *
  omega
theorem privateDuplicate : (privateInput layout).representation.encoding.words + (privateInput layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := privateInput_le layout; omega)
def retainedInput := (Read.input layout).prod (Reply.range layout) (layout.fits_of_le (by
  change (Read.input layout).representation.encoding.words + 1 ≤ _
  have := Read.input_le layout
  unfold Layouts.width at *
  omega))
def retainedOutput := (Read.output layout).prod (Reply.range layout) (layout.fits_of_le (by
  change (Read.output layout).representation.encoding.words + 1 ≤ _
  have := Reply.response_le layout
  unfold Layouts.width at *
  omega))
theorem retainedOutput_le : (retainedOutput layout).representation.encoding.words ≤ 4 * layout.width := by
  change (Read.output layout).representation.encoding.words + 1 ≤ _
  have := Reply.response_le layout
  unfold Layouts.width at *
  omega

def tag : Constructed (Reply.range layout) layout.counter (fun n => n + 2) :=
  (Constructed.addLiteral (2 ^ w - 2) 2 layout.wordFits (by have := layout.wordFits; omega)).viewOutput layout.counter
    (fun n valid => by
      change n < 2 ^ w - 2 at valid
      change n + 2 < 2 ^ w
      omega) (fun _ => rfl)
def inputRange : Constructed (privateInput layout) (Reply.range layout) Prod.fst :=
  Constructed.first (Reply.range layout) (Read.store layout) layout.wordFits (privateInput layout).representation.fits
def inputStore : Constructed (privateInput layout) (Read.store layout) Prod.snd :=
  Constructed.second (Reply.range layout) (Read.store layout) layout.wordFits (privateInput layout).representation.fits
def inputTag : Constructed (privateInput layout) layout.counter (fun value => value.1 + 2) :=
  (inputRange layout).then (tag layout)

def swapReply : Constructed (retainedOutput layout) (Reply.input layout) (fun value => (value.2, value.1)) :=
  (Constructed.second (Read.output layout) (Reply.range layout) layout.wordFits (retainedOutput layout).representation.fits).pair
    (Constructed.first (Read.output layout) (Reply.range layout) layout.wordFits (retainedOutput layout).representation.fits) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by
      change (retainedOutput layout).representation.encoding.words + (retainedOutput layout).representation.encoding.words ≤ _
      have := retainedOutput_le layout
      omega))
    (layout.fits_of_le (by
      change 1 + (retainedOutput layout).representation.encoding.words ≤ _
      have := retainedOutput_le layout
      unfold Layouts.width at *
      omega))
    (Reply.input layout).representation.fits
def finish : Constructed (retainedOutput layout) (Reply.privateOutput layout)
    (fun value => Reply.privateSource (value.2, value.1)) :=
  (swapReply layout).then (Reply.privateDecoder layout)
theorem finish_buffers : (finish layout).buffers = 6 := by
  change max 3 (Reply.privateDecoder layout).buffers = 6
  rw [Reply.private_buffers]
  rfl

variable [Zero F] (zeroValid : layout.scalar.valid 0)

def fallback : layout.entry.Value :=
  ⟨(0, 0, 0), by change 0 < 2 ^ w; positivity, zeroValid, by change 0 < 2 ^ w; positivity⟩
def scalarTail : Constructed (Read.store layout) (Read.tail layout) (fun value => ((0, 0, 0), value)) :=
  (Constructed.constant (Read.store layout) layout.entry (fallback layout zeroValid) layout.wordFits).pair
    (Constructed.identity (Read.store layout) (width_pos layout.wordFits)) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 0 < _; positivity)
    (layout.fits_of_le (by have := Read.store_le layout; omega))
    (Read.tail layout).representation.fits (Read.tail layout).representation.fits
def scalarPacket : Constructed (Read.store layout) (Read.input layout) (fun value => (1, (0, 0, 0), value)) :=
  (Constructed.constant (Read.store layout) layout.counter ⟨1, by change 1 < 2 ^ w; have := layout.wordFits; omega⟩ layout.wordFits).pair
    (scalarTail layout zeroValid) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by have := Read.store_le layout; omega))
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := Read.store_le layout; unfold Layouts.width at *; omega))
    (Read.input layout).representation.fits
def privateTail : Constructed (privateInput layout) (Read.tail layout) (fun value => ((0, 0, 0), value.2)) :=
  (inputStore layout).then (scalarTail layout zeroValid)
def privatePacket : Constructed (privateInput layout) (Read.input layout) (fun value => (value.1 + 2, (0, 0, 0), value.2)) :=
  (inputTag layout).pair (privateTail layout zeroValid) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega) (by change 3 < _; have := layout.wordFits; omega)
    (privateDuplicate layout)
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := privateInput_le layout; unfold Layouts.width at *; omega))
    (Read.input layout).representation.fits
def prepare : Constructed (privateInput layout) (retainedInput layout) (fun value => ((value.1 + 2, (0, 0, 0), value.2), value.1)) :=
  (privatePacket layout zeroValid).pair (inputRange layout) layout.wordFits
    (by change 4 < _; have := layout.wordFits; omega) (by change 2 < _; have := layout.wordFits; omega)
    (privateDuplicate layout)
    (layout.fits_of_le (by have := Read.input_le layout; have := privateInput_le layout; omega))
    (retainedInput layout).representation.fits
theorem prepare_buffers : (prepare layout zeroValid).buffers = 5 := rfl
theorem scalarPacket_buffers : (scalarPacket layout zeroValid).buffers = 4 := rfl

def rawPrivate (n : Nat) (state : Schnorr.RawTape.State F) :=
  (n, state.saved, state.remaining)
def rawScalar (state : Schnorr.RawTape.State F) := (state.saved, state.remaining)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Caller
