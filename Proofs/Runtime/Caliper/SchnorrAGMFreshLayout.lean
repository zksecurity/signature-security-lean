import Proofs.Runtime.Caliper.SchnorrAGMCacheLayout
import Proofs.Runtime.Caliper.BooleanOr

/-! Runtime frames for fresh Schnorr AGM challenges. All intermediate frames
fit the original scheme's declared storage reservation. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
open Caliper BoundedSource
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

abbrev Input := layout.scalar.Value × (Cache.saved layout).Value

def input : Representation w (Input layout) :=
  layout.scalar.representation.prod (Cache.saved layout).representation
    (layout.fits_of_le (by
      change _ + ((_ + _) + 1) ≤ _
      dsimp only [Layouts.width, storageWidth]; omega))

theorem input_words : (input layout).encoding.words = 3 * layout.scalar.representation.encoding.words + 1 := by
  change _ + ((_ + _) + 1) = _; omega

def adding : Representation w (layout.affine.Value × Input layout) :=
  layout.affine.representation.prod (input layout) (layout.fits_of_le (by
    rw [Layouts.affine_words, input_words]; dsimp only [Layouts.width, storageWidth]; omega))
def added : Representation w (layout.scalar.Value × Input layout) :=
  layout.scalar.representation.prod (input layout) (layout.fits_of_le (by
    rw [input_words]; dsimp only [Layouts.width, storageWidth]; omega))
def flagged : Representation w (Bool × Input layout) :=
  (Representation.boolean w (width_pos layout.wordFits)).prod (input layout) (layout.fits_of_le (by
    change 1 + _ ≤ _; rw [input_words]; dsimp only [Layouts.width, storageWidth]; omega))
def merging : Representation w ((Bool × Bool) × Input layout) :=
  (Boolean.pair layout.wordFits).prod (input layout) (layout.fits_of_le (by
    change (1 + 1) + _ ≤ _; rw [input_words]; dsimp only [Layouts.width, storageWidth]; omega))

def addValue (value : Input layout) : layout.affine.Value × Input layout :=
  (⟨(value.2.val.1.2, value.1.val), value.2.property.1.2, value.1.property⟩, value)
def mergeValue (value : Bool × Input layout) : (Bool × Bool) × Input layout :=
  ((value.2.2.val.2, value.1), value.2)
def finishValue (value : Bool × Input layout) : layout.entry.Value × (Cache.saved layout).Value :=
  (⟨(value.2.1.val, true, value.2.2.val.1), value.2.1.property, trivial, value.2.2.property.1⟩,
    ⟨(value.2.2.val.1, value.1), value.2.2.property.1, trivial⟩)

theorem sizes :
    (input layout).encoding.words ≤ 4 * layout.width ∧
    (adding layout).encoding.words ≤ 8 * layout.width ∧
    (added layout).encoding.words ≤ 8 * layout.width ∧
    (flagged layout).encoding.words ≤ 8 * layout.width ∧
    (merging layout).encoding.words ≤ 8 * layout.width ∧
    (Cache.model layout).freshOutput.encoding.words ≤ 8 * layout.width := by
  change _ ≤ _ ∧ layout.affine.representation.encoding.words + _ ≤ _ ∧
    layout.scalar.representation.encoding.words + _ ≤ _ ∧ 1 + _ ≤ _ ∧ (1 + 1) + _ ≤ _ ∧
    layout.entry.representation.encoding.words + (layout.affine.representation.encoding.words + 1) ≤ _
  rw [input_words, Layouts.affine_words, Layouts.entry_words]
  dsimp only [Layouts.width, storageWidth]
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
