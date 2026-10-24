import Proofs.Runtime.Caliper.SchnorrROMTapePop
import Proofs.Runtime.Caliper.ConstructedStorage

/-! Storage for one replay query. A reserved saved-tape slot admits a miss;
the reservation is a source invariant, not an uncharged runtime decision. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

abbrev Input (F : Type) := Nat × Schnorr.TapeCell F × List (Schnorr.TapeCell F) × List (Schnorr.TapeCell F)
abbrev Frame (F : Type) := (Bool × Schnorr.TapeCell F × List (Schnorr.TapeCell F)) × Nat × List (Schnorr.TapeCell F)
abbrev Output (F : Type) := Schnorr.TapeCell F × List (Schnorr.TapeCell F) × List (Schnorr.TapeCell F)

def list := layout.list layout.capacity (by omega)
theorem list_le : (list layout).representation.encoding.words ≤ layout.width := layout.list_le layout.capacity (by omega)
def saved := (list layout).restrict (fun cells => cells.length < layout.capacity)
theorem saved_le : (saved layout).representation.encoding.words ≤ layout.width := list_le layout
def store := (saved layout).prod (list layout)
  (layout.fits_of_le (by have := saved_le layout; have := list_le layout; omega))
theorem store_le : (store layout).representation.encoding.words ≤ 2 * layout.width := by
  change (saved layout).representation.encoding.words + (list layout).representation.encoding.words ≤ _
  have := saved_le layout; have := list_le layout; omega
def tail := layout.entry.prod (store layout)
  (layout.fits_of_le (by have := layout.entry_le; have := store_le layout; omega))
theorem tail_le : (tail layout).representation.encoding.words ≤ 3 * layout.width := by
  change layout.entry.representation.encoding.words + (store layout).representation.encoding.words ≤ _
  have := layout.entry_le; have := store_le layout; omega
def input : Layout w (Input F) := layout.counter.prod (tail layout)
  (layout.fits_of_le (by rw [Layouts.counter_words]; have := tail_le layout; unfold Layouts.width at *; omega))
theorem input_le : (input layout).representation.encoding.words ≤ 4 * layout.width := by
  change 1 + (tail layout).representation.encoding.words ≤ _
  have := tail_le layout; unfold Layouts.width at *; omega
def retained := layout.counter.prod (saved layout)
  (layout.fits_of_le (by rw [Layouts.counter_words]; have := saved_le layout; unfold Layouts.width at *; omega))
theorem retained_le : (retained layout).representation.encoding.words ≤ 2 * layout.width := by
  change 1 + (saved layout).representation.encoding.words ≤ _
  have := saved_le layout; unfold Layouts.width at *; omega
def frame : Layout w (Frame F) := (Pop.state layout layout.capacity (by omega)).prod (retained layout)
  (layout.fits_of_le (by have := Pop.state_le layout layout.capacity (by omega); have := retained_le layout; omega))
theorem frame_le : (frame layout).representation.encoding.words ≤ 3 * layout.width := by
  change (Pop.state layout layout.capacity (by omega)).representation.encoding.words + (retained layout).representation.encoding.words ≤ _
  have := Pop.state_le layout layout.capacity (by omega); have := retained_le layout; omega
theorem frameDuplicate : (frame layout).representation.encoding.words + (frame layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := frame_le layout; omega)
theorem frameTag : 1 + (frame layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := frame_le layout; unfold Layouts.width at *; omega)
def choice := (frame layout).sum (frame layout) (width_pos layout.wordFits) (by simpa using frameTag layout)
def drawInput := layout.counter.prod (frame layout)
  (layout.fits_of_le (by rw [Layouts.counter_words]; have := frame_le layout; unfold Layouts.width at *; omega))
def drawn := layout.entry.prod (frame layout)
  (layout.fits_of_le (by have := layout.entry_le; have := frame_le layout; omega))
theorem drawn_le : (drawn layout).representation.encoding.words ≤ 4 * layout.width := by
  change layout.entry.representation.encoding.words + (frame layout).representation.encoding.words ≤ _
  have := layout.entry_le; have := frame_le layout; omega
def tapes := (list layout).prod (list layout)
  (layout.fits_of_le (by have := list_le layout; omega))
theorem tapes_le : (tapes layout).representation.encoding.words ≤ 2 * layout.width := by
  change (list layout).representation.encoding.words + (list layout).representation.encoding.words ≤ _
  have := list_le layout; omega
def output : Layout w (Output F) := layout.entry.prod (tapes layout)
  (layout.fits_of_le (by have := layout.entry_le; have := tapes_le layout; omega))

def appendLayout : ListSnoc.Layouts w (Schnorr.TapeCell F) where
  entry := layout.entry
  capacity := layout.capacity
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := layout.fits_of_le (by rw [Layouts.entry_words]; unfold Layouts.width; nlinarith)

theorem inputDuplicate : (input layout).representation.encoding.words + (input layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := input_le layout; omega)
theorem drawnDuplicate : (drawn layout).representation.encoding.words + (drawn layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := drawn_le layout; omega)

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Read
