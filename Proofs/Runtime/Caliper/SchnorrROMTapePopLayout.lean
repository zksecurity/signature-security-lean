import Proofs.Runtime.Caliper.SchnorrROMTapeReset
import Proofs.Runtime.Caliper.Constructed
import Proofs.Runtime.Caliper.LookupLayout

/-! Replay-pop layouts use the same original cells and tape capacity as reset.
The fold environment contains the runtime family tag; no family-sized dispatch
table is constructed. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Pop
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

def payload (n : Nat) (small : n ≤ layout.capacity + 1) :=
  layout.entry.prod (layout.list n small)
    (layout.fits_of_le (by have := layout.entry_le; have := layout.list_le n small; omega))
def state (n : Nat) (small : n ≤ layout.capacity + 1) :=
  layout.boolean.prod (payload layout n small) (layout.fits_of_le (by
    change 1 + (layout.entry.representation.encoding.words + (layout.list n small).representation.encoding.words) ≤ _
    have := layout.entry_le; have := layout.list_le n small; unfold Layouts.width at *; omega))
def states (i : Fin (layout.capacity + 1)) := state layout i.val (by omega)
def tail (i : Fin (layout.capacity + 1)) := (states layout i).prod layout.counter
  (layout.fits_of_le (by
    change (1 + (layout.entry.representation.encoding.words + (1 + i.val * layout.entry.representation.encoding.words))) + 1 ≤ _
    have := Nat.mul_le_mul_right layout.entry.representation.encoding.words (show i.val ≤ layout.capacity + 1 by omega)
    rw [Layouts.entry_words] at *
    unfold Layouts.width
    nlinarith))
theorem state_words (n : Nat) (small : n ≤ layout.capacity + 1) :
    (state layout n small).representation.encoding.words = 2 + (n + 1) * layout.entry.representation.encoding.words := by
  change 1 + (_ + (1 + n * _)) = _; ring
theorem payload_le (n : Nat) (small : n ≤ layout.capacity + 1) :
    (payload layout n small).representation.encoding.words ≤ layout.width := by
  change _ + (1 + n * layout.entry.representation.encoding.words) ≤ _
  have := Nat.mul_le_mul_right layout.entry.representation.encoding.words small
  rw [Layouts.entry_words] at *
  unfold Layouts.width
  nlinarith
theorem state_le (n : Nat) (small : n ≤ layout.capacity + 1) :
    (state layout n small).representation.encoding.words ≤ layout.width := by
  rw [state_words]
  have := Nat.mul_le_mul_right layout.entry.representation.encoding.words small
  rw [Layouts.entry_words] at *
  unfold Layouts.width
  nlinarith
theorem tail_le (i : Fin (layout.capacity + 1)) :
    (tail layout i).representation.encoding.words ≤ 2 * layout.width := by
  have bound : (states layout i).representation.encoding.words ≤ layout.width := state_le layout i.val (by omega)
  change (states layout i).representation.encoding.words + 1 ≤ _
  unfold Layouts.width at *
  omega
theorem argFits (i : Fin layout.capacity) :
    layout.entry.representation.encoding.words + (states layout i.castSucc).representation.encoding.words +
      layout.counter.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by
    have bound : (states layout i.castSucc).representation.encoding.words ≤ layout.width := state_le layout i.val (by omega)
    have := layout.entry_le; rw [Layouts.counter_words]; unfold Layouts.width at *; omega)
theorem frameFits (i : Fin (layout.capacity + 1)) :
    1 + (layout.capacity - i.val) * layout.entry.representation.encoding.words +
      (states layout i).representation.encoding.words + 2 * layout.counter.representation.encoding.words < 2 ^ w := by
  apply layout.fits_of_le
  change 1 + (layout.capacity - i.val) * layout.entry.representation.encoding.words +
    (1 + (layout.entry.representation.encoding.words + (1 + i.val * layout.entry.representation.encoding.words))) + 2 * 1 ≤ _
  have combined : (layout.capacity - i.val) * layout.entry.representation.encoding.words +
      i.val * layout.entry.representation.encoding.words = layout.capacity * layout.entry.representation.encoding.words := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  have := layout.list_le layout.capacity (by omega)
  have := layout.entry_le
  rw [Layouts.list_words] at *
  unfold Layouts.width at *
  omega
def bodyInput (i : Fin layout.capacity) :=
  FoldImplementation.bodyInput layout.entry (states layout i.castSucc) layout.counter (argFits layout i)
def frame := FoldImplementation.input layout.entry (states layout 0) layout.counter layout.capacity
  (by have := layout.countFits; omega) (frameFits layout 0)
theorem body_le (i : Fin layout.capacity) : (bodyInput layout i).representation.encoding.words ≤ 3 * layout.width := by
  change layout.entry.representation.encoding.words + (tail layout i.castSucc).representation.encoding.words ≤ _
  have := layout.entry_le; have := tail_le layout i.castSucc; omega
theorem duplicateFits (i : Fin layout.capacity) :
    (bodyInput layout i).representation.encoding.words + (bodyInput layout i).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := body_le layout i; omega)
theorem tagFits (i : Fin layout.capacity) : 1 + (bodyInput layout i).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := body_le layout i; unfold Layouts.width at *; omega)

def reversal : ListReverse.Layouts w (Schnorr.TapeCell F) where
  entry := layout.entry
  capacity := layout.capacity
  wordFits := layout.wordFits
  countFits := by have := layout.countFits; omega
  storageFits := layout.fits_of_le (by rw [Layouts.entry_words]; unfold Layouts.width; nlinarith)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Pop
