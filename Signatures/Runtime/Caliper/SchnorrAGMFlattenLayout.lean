import Signatures.Runtime.Caliper.AttachRowsBounds
import Signatures.Runtime.Caliper.BLSAccumulateNames
import Signatures.Runtime.SchnorrAGMFlatten

/-! Bounded affine flattening with independent basis and coefficient capacities.
Only the chronological basis is traversed; the mathematical scalar domain is
not enumerated and surplus coefficients do not create new rows. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
open Caliper BoundedSource

structure Layouts (w : Nat) (F : Type) where
  scalar : Layout w F
  capacity : Nat
  coefficients : Nat
  wordFits : 16 < 2 ^ w
  counterFits : capacity + 2 ≤ 2 ^ w
  coefficientCountFits : coefficients < 2 ^ w
  storageFits : 32 * (4 + (capacity + 1) * (3 * scalar.representation.encoding.words) +
    (coefficients + 1) * scalar.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {F : Type} (layout : Layouts w F)

def width : Nat := 4 + (layout.capacity + 1) * (3 * layout.scalar.representation.encoding.words) +
  (layout.coefficients + 1) * layout.scalar.representation.encoding.words

theorem fits_of_le {words : Nat} (bound : words ≤ 32 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def arithmetic : BLSAccumulate.Layouts w F where
  scalar := layout.scalar
  wordFits := layout.wordFits
  storageFits := layout.fits_of_le (by dsimp only [width]; nlinarith)
def affine : Layout w (F × F) := layout.arithmetic.pair
@[simp] theorem affine_words : layout.affine.representation.encoding.words = 2 * layout.scalar.representation.encoding.words :=
  BLSAccumulate.Layouts.pair_words layout.arithmetic

def attach : AttachRows.Layouts w (F × F) F where
  key := layout.affine
  value := layout.scalar
  capacity := layout.capacity
  coefficients := layout.coefficients
  wordFits := layout.wordFits
  counterFits := layout.counterFits
  coefficientCountFits := layout.coefficientCountFits
  storageFits := layout.fits_of_le (by rw [affine_words]; dsimp only [width]; nlinarith)

theorem attach_width : layout.attach.width = layout.width := by
  change 4 + (layout.capacity + 1) * (layout.affine.representation.encoding.words + layout.scalar.representation.encoding.words) +
    (layout.coefficients + 1) * layout.scalar.representation.encoding.words = _
  rw [affine_words]
  dsimp only [width]
  ring

def input : Layout w (List (F × F) × List F) := layout.attach.keys.prod layout.attach.values
  (layout.fits_of_le (by have := layout.attach.base_sizes; rw [attach_width] at this; omega))
def rows : Layout w (List ((F × F) × F)) := layout.attach.output
def unit (_layout : Layouts w F) : Layout w Unit := DataImplementation.unitLayout w

theorem argFits : layout.attach.row.representation.encoding.words + layout.affine.representation.encoding.words +
    layout.unit.representation.encoding.words < 2 ^ w := layout.fits_of_le (by
  change (layout.affine.representation.encoding.words + layout.scalar.representation.encoding.words) +
    layout.affine.representation.encoding.words + 0 ≤ _
  rw [affine_words]; dsimp only [width]; nlinarith)
def body := FoldImplementation.bodyInput layout.attach.row layout.affine layout.unit layout.argFits

theorem foldFits : 1 + layout.capacity * layout.attach.row.representation.encoding.words +
    layout.affine.representation.encoding.words + 2 * layout.unit.representation.encoding.words < 2 ^ w := layout.fits_of_le (by
  change 1 + layout.capacity * (layout.affine.representation.encoding.words + layout.scalar.representation.encoding.words) +
    layout.affine.representation.encoding.words + 2 * 0 ≤ _
  rw [affine_words]; dsimp only [width]; nlinarith)
def frame := FoldImplementation.input layout.attach.row layout.affine layout.unit layout.capacity layout.attach.countFits layout.foldFits

theorem sizes : layout.input.representation.encoding.words ≤ 2 * layout.width ∧
    layout.attach.input.representation.encoding.words ≤ layout.width ∧
    layout.rows.representation.encoding.words ≤ layout.width ∧
    layout.frame.representation.encoding.words ≤ 2 * layout.width := by
  have base := layout.attach.base_sizes
  rw [attach_width] at base
  have result := AttachRows.output_size layout.attach
  rw [attach_width] at result
  have scalar : layout.affine.representation.encoding.words ≤ layout.width := base.1
  change layout.attach.keys.representation.encoding.words + layout.attach.values.representation.encoding.words ≤ _ ∧ _ ∧
    1 + layout.capacity * layout.attach.row.representation.encoding.words ≤ _ ∧
    (1 + layout.capacity * layout.attach.row.representation.encoding.words) + (layout.affine.representation.encoding.words + 0) ≤ _
  change 1 + layout.capacity * layout.attach.row.representation.encoding.words ≤ _ at result
  omega
end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
