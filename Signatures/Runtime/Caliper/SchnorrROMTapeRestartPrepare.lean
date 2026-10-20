import Signatures.Runtime.Caliper.SchnorrROMTapeFreshPrepare

/-! Charged preparation of a replay restart. The input contains the selected
slot, replacement scalar and both old tapes. Instructions construct the
challenge cell and retain the saved tape; the old remaining tape is discarded. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Restart
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

abbrev Input (F : Type) := Nat × F × List (Schnorr.TapeCell F) × List (Schnorr.TapeCell F)
def tail := layout.scalar.prod (Read.tapes layout) (layout.fits_of_le (by
  have scalar := layout.entry_le
  rw [Layouts.entry_words] at scalar
  have := Read.tapes_le layout
  omega))
theorem tail_le : (tail layout).representation.encoding.words ≤ 3 * layout.width := by
  change layout.scalar.representation.encoding.words + (Read.tapes layout).representation.encoding.words ≤ _
  have scalar := layout.entry_le
  rw [Layouts.entry_words] at scalar
  have := Read.tapes_le layout
  omega
def input : Layout w (Input F) := layout.counter.prod (tail layout) (layout.fits_of_le (by
  rw [Layouts.counter_words]
  have := tail_le layout
  unfold Layouts.width at *
  omega))
theorem input_le : (input layout).representation.encoding.words ≤ 4 * layout.width := by
  change 1 + (tail layout).representation.encoding.words ≤ _
  have := tail_le layout
  unfold Layouts.width at *
  omega
theorem inputDuplicate : (input layout).representation.encoding.words + (input layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := input_le layout; omega)

def inputSlot : Constructed (input layout) layout.counter Prod.fst :=
  Constructed.first layout.counter (tail layout) layout.wordFits (input layout).representation.fits
def inputTail : Constructed (input layout) (tail layout) Prod.snd :=
  Constructed.second layout.counter (tail layout) layout.wordFits (input layout).representation.fits
def inputAnswer : Constructed (input layout) layout.scalar (fun value => value.2.1) :=
  (inputTail layout).then
    (Constructed.first layout.scalar (Read.tapes layout) layout.wordFits (tail layout).representation.fits)
def inputTapes : Constructed (input layout) (Read.tapes layout) (fun value => value.2.2) :=
  (inputTail layout).then
    (Constructed.second layout.scalar (Read.tapes layout) layout.wordFits (tail layout).representation.fits)
def inputSaved : Constructed (input layout) (Read.list layout) (fun value => value.2.2.1) :=
  (inputTapes layout).then
    (Constructed.first (Read.list layout) (Read.list layout) layout.wordFits (Read.tapes layout).representation.fits)
def inputCell : Constructed (input layout) layout.entry (fun value => (1, value.2.1, 0)) :=
  (inputAnswer layout).then (Fresh.scalarCell layout)
theorem inputCell_buffers : (inputCell layout).buffers = 4 := by
  change max (inputAnswer layout).buffers (Fresh.scalarCell layout).buffers = 4
  rw [Fresh.scalarCell_buffers]
  rfl
def preparedTail : Constructed (input layout) layout.resetTail (fun value => ((1, value.2.1, 0), value.2.2.1)) :=
  (inputCell layout).pair (inputSaved layout) layout.wordFits
    (by rw [inputCell_buffers]; have := layout.wordFits; omega)
    (by change 2 < _; have := layout.wordFits; omega)
    (inputDuplicate layout)
    (layout.fits_of_le (by have := layout.entry_le; have := input_le layout; omega))
    layout.resetTail.representation.fits
theorem preparedTail_buffers : (preparedTail layout).buffers = 5 := by
  change max 2 (max (inputCell layout).buffers (inputSaved layout).buffers) + 1 = 5
  rw [inputCell_buffers]
  rfl
def prepare : Constructed (input layout) layout.resetInput (fun value => (value.1, (1, value.2.1, 0), value.2.2.1)) :=
  (inputSlot layout).pair (preparedTail layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega)
    (by rw [preparedTail_buffers]; have := layout.wordFits; omega)
    (inputDuplicate layout)
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := input_le layout; unfold Layouts.width at *; omega))
    layout.resetInput.representation.fits
theorem prepare_buffers : (prepare layout).buffers = 6 := by
  change max 2 (max (inputSlot layout).buffers (preparedTail layout).buffers) + 1 = 6
  rw [preparedTail_buffers]
  rfl

def rawInput (slot : Nat) (answer : F) (state : Schnorr.RawTape.State F) : Input F :=
  (slot, answer, state.saved, state.remaining)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Restart
