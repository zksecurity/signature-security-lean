import Proofs.Runtime.Caliper.SchnorrROMTapeReadSource
import Proofs.Runtime.Caliper.ConstructedArithmetic
import Proofs.Runtime.Caliper.ConstructedBudget

/-! Executed caller reply decoding. Private replies retain their requested
range, compute the original natural remainder and copy both tapes. Challenge
replies project the scalar and copy both tapes. Decoding is charged code, and
does not assume a natural-valued cell was already valid for its query. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Reply
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def range : Layout w Nat := Layout.counter w (2 ^ w - 2) (width_pos layout.wordFits) (Nat.sub_le _ _)
def one : Layout w Nat := Layout.counter w 2 (width_pos layout.wordFits) (by have := layout.wordFits; omega)
def addInput := (range layout).prod (one layout) (by change 1 + 1 < _; have := layout.wordFits; omega)
def addArgs : Constructed (range layout) (addInput layout) (fun n => (n, 1)) :=
  (Constructed.identity (range layout) (width_pos layout.wordFits)).pair
    (Constructed.constant (range layout) (one layout) ⟨1, by change 1 < 2; decide⟩ layout.wordFits) layout.wordFits
    (by change 0 < _; positivity) (by change 2 < _; have := layout.wordFits; omega)
    (addInput layout).representation.fits (addInput layout).representation.fits (addInput layout).representation.fits
def increment : Constructed (range layout) layout.counter (fun n => n + 1) :=
  ((addArgs layout).then (Constructed.add (2 ^ w - 2) 2 layout.wordFits
    (by have := layout.wordFits; omega))).viewOutput layout.counter
      (fun n valid => by
        change n < 2 ^ w - 2 at valid
        change n + 1 < 2 ^ w
        omega) (fun _ => rfl)
theorem increment_buffers : (increment layout).buffers = 3 := rfl

theorem response_le : (Read.output layout).representation.encoding.words ≤ 3 * layout.width := by
  change layout.entry.representation.encoding.words + (Read.tapes layout).representation.encoding.words ≤ _
  have := layout.entry_le
  have := Read.tapes_le layout
  omega
def input := (range layout).prod (Read.output layout) (layout.fits_of_le (by
  change 1 + (Read.output layout).representation.encoding.words ≤ _
  have := response_le layout
  unfold Layouts.width at *
  omega))
theorem input_le : (input layout).representation.encoding.words ≤ 4 * layout.width := by
  change 1 + (Read.output layout).representation.encoding.words ≤ _
  have := response_le layout
  unfold Layouts.width at *
  omega
theorem inputDuplicate : (input layout).representation.encoding.words + (input layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := input_le layout; omega)
def pair := layout.counter.prod layout.counter (by change 1 + 1 < _; have := layout.wordFits; omega)
def privateTail := layout.counter.prod (Read.tapes layout) (layout.fits_of_le (by
  rw [Layouts.counter_words]
  have := Read.tapes_le layout
  unfold Layouts.width at *
  omega))
theorem privateTail_le : (privateTail layout).representation.encoding.words ≤ 3 * layout.width := by
  change 1 + (Read.tapes layout).representation.encoding.words ≤ _
  have := Read.tapes_le layout
  unfold Layouts.width at *
  omega
def privateRaw := (range layout).prod (privateTail layout) (layout.fits_of_le (by
  change 1 + (privateTail layout).representation.encoding.words ≤ _
  have := privateTail_le layout
  unfold Layouts.width at *
  omega))
def privateOutput := (privateRaw layout).restrict (fun value => value.2.1 ≤ value.1)
def scalarOutput := layout.scalar.prod (Read.tapes layout) (layout.fits_of_le (by
  have scalar := layout.entry_le
  rw [Layouts.entry_words] at scalar
  have := Read.tapes_le layout
  omega))

def responseCell : Constructed (Read.output layout) layout.entry Prod.fst :=
  Constructed.first layout.entry (Read.tapes layout) layout.wordFits (Read.output layout).representation.fits
def responsePayload : Constructed (Read.output layout) layout.payload (fun value => value.1.2) :=
  (responseCell layout).then (Constructed.second layout.counter layout.payload layout.wordFits layout.entry.representation.fits)
def responseNatural : Constructed (Read.output layout) layout.counter (fun value => value.1.2.2) :=
  (responsePayload layout).then (Constructed.second layout.scalar layout.counter layout.wordFits layout.payload.representation.fits)
def responseScalar : Constructed (Read.output layout) layout.scalar (fun value => value.1.2.1) :=
  (responsePayload layout).then (Constructed.first layout.scalar layout.counter layout.wordFits layout.payload.representation.fits)
def responseTapes : Constructed (Read.output layout) (Read.tapes layout) Prod.snd :=
  Constructed.second layout.entry (Read.tapes layout) layout.wordFits (Read.output layout).representation.fits

def inputRange : Constructed (input layout) (range layout) Prod.fst :=
  Constructed.first (range layout) (Read.output layout) layout.wordFits (input layout).representation.fits
def inputResponse : Constructed (input layout) (Read.output layout) Prod.snd :=
  Constructed.second (range layout) (Read.output layout) layout.wordFits (input layout).representation.fits
def inputNatural : Constructed (input layout) layout.counter (fun value => value.2.1.2.2) :=
  (inputResponse layout).then (responseNatural layout)
def inputTapes : Constructed (input layout) (Read.tapes layout) (fun value => value.2.2) :=
  (inputResponse layout).then (responseTapes layout)
def divisor : Constructed (input layout) layout.counter (fun value => value.1 + 1) :=
  (inputRange layout).then (increment layout)
theorem divisor_buffers : (divisor layout).buffers = 3 := by
  change max 2 (increment layout).buffers = 3
  rw [increment_buffers]
  rfl
def moduloInput : Constructed (input layout) (pair layout) (fun value => (value.2.1.2.2, value.1 + 1)) :=
  (inputNatural layout).pair (divisor layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega)
    (by rw [divisor_buffers]; have := layout.wordFits; omega) (inputDuplicate layout)
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := input_le layout; unfold Layouts.width at *; omega))
    (pair layout).representation.fits
theorem moduloInput_budget : (moduloInput layout).budget =
    Budget.pair (input layout).representation.encoding.words 1 1 (inputNatural layout).budget (divisor layout).budget := by
  unfold moduloInput
  erw [Constructed.pair_budget]
  rfl
theorem moduloInput_buffers : (moduloInput layout).buffers = 4 := by
  change max 2 (max 2 (divisor layout).buffers) + 1 = 4
  rw [divisor_buffers]
  rfl
def answer : Constructed (input layout) layout.counter (fun value => value.2.1.2.2 % (value.1 + 1)) :=
  (moduloInput layout).then (Constructed.modulo (2 ^ w) (2 ^ w) layout.wordFits le_rfl le_rfl)
theorem answer_buffers : (answer layout).buffers = 4 := by
  change max (moduloInput layout).buffers 1 = 4
  rw [moduloInput_buffers]
  rfl
def finishedTail : Constructed (input layout) (privateTail layout)
    (fun value => (value.2.1.2.2 % (value.1 + 1), value.2.2)) :=
  (answer layout).pair (inputTapes layout) layout.wordFits
    (by rw [answer_buffers]; have := layout.wordFits; omega)
    (by change 2 < _; have := layout.wordFits; omega) (inputDuplicate layout)
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := input_le layout; unfold Layouts.width at *; omega))
    (privateTail layout).representation.fits
theorem finishedTail_buffers : (finishedTail layout).buffers = 5 := by
  change max 2 (max (answer layout).buffers 2) + 1 = 5
  rw [answer_buffers]
  rfl
def privateSource (value : Nat × Read.Output F) : Nat × Nat × List (Schnorr.TapeCell F) × List (Schnorr.TapeCell F) :=
  (value.1, value.2.1.2.2 % (value.1 + 1), value.2.2)
def privatePacket : Constructed (input layout) (privateRaw layout) privateSource :=
  (inputRange layout).pair (finishedTail layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega)
    (by rw [finishedTail_buffers]; have := layout.wordFits; omega) (inputDuplicate layout)
    (layout.fits_of_le (by change 1 + (input layout).representation.encoding.words ≤ _; have := input_le layout; unfold Layouts.width at *; omega))
    (privateRaw layout).representation.fits
def privateDecoder : Constructed (input layout) (privateOutput layout) privateSource :=
  (privatePacket layout).viewOutput (privateOutput layout)
    (fun value valid => ⟨(privatePacket layout).implementation.preserves value valid,
      Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))⟩) (fun _ => rfl)
theorem private_buffers : (privateDecoder layout).buffers = 6 := by
  change max 2 (max 2 (finishedTail layout).buffers) + 1 = 6
  rw [finishedTail_buffers]
  rfl

def scalarSource (value : Read.Output F) : F × List (Schnorr.TapeCell F) × List (Schnorr.TapeCell F) :=
  (value.1.2.1, value.2)
def scalarDecoder : Constructed (Read.output layout) (scalarOutput layout) scalarSource :=
  (responseScalar layout).pair (responseTapes layout) layout.wordFits
    (by change 2 < _; have := layout.wordFits; omega)
    (by change 2 < _; have := layout.wordFits; omega)
    (layout.fits_of_le (by have := response_le layout; omega))
    (layout.fits_of_le (by
      have scalar := layout.entry_le
      rw [Layouts.entry_words] at scalar
      have := response_le layout
      omega))
    (scalarOutput layout).representation.fits
theorem scalar_buffers : (scalarDecoder layout).buffers = 3 := rfl

theorem private_source (n : Nat) (value : Read.Output F) :
    privateSource (n, value) = (n, (Schnorr.RawTape.decode (.inl n) value.1).val, value.2) := rfl
theorem scalar_source (value : Read.Output F) :
    scalarSource value = (Schnorr.RawTape.decode (.inr ()) value.1, value.2) := rfl

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Reply
