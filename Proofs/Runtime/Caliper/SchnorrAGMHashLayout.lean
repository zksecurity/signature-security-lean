import Proofs.Runtime.Caliper.SchnorrAGMFlattenBounds
import Proofs.Runtime.Caliper.SchnorrAGMReadMemory

/-! Hash-request frames retain the current key and complete source state while
flattening the supplied coefficient list. Cache admission depends on the key
and table, so it can be established before computing the affine explanation. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native

structure Layouts (w : Nat) (M F G : Type) (qH qS : Nat) where
  scheme : SchnorrAGM.Layouts w M F G qH qS
  coefficients : Nat
  counterFits : qS + 4 ≤ 2 ^ w
  coefficientCountFits : coefficients < 2 ^ w
  storageFits : 64 * (scheme.width + 4 + (qS + 3) * (3 * scheme.scalar.representation.encoding.words) +
    (coefficients + 1) * scheme.scalar.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def width : Nat := layout.scheme.width + 4 + (qS + 3) * (3 * layout.scheme.scalar.representation.encoding.words) +
  (layout.coefficients + 1) * layout.scheme.scalar.representation.encoding.words

theorem fits_of_le {words : Nat} (bound : words ≤ 64 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def flat : Flatten.Layouts w F where
  scalar := layout.scheme.scalar
  capacity := qS + 2
  coefficients := layout.coefficients
  wordFits := layout.scheme.wordFits
  counterFits := by have := layout.counterFits; omega
  coefficientCountFits := layout.coefficientCountFits
  storageFits := layout.fits_of_le (by
    dsimp only [width]
    rw [show qS + 2 + 1 = qS + 3 by omega]
    omega)

theorem width_eq : layout.width = layout.scheme.width + layout.flat.width := by
  dsimp only [width, flat, Flatten.Layouts.width]
  ring

theorem scheme_size : layout.scheme.key.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤ layout.scheme.width := by
  have components := Read.components layout.scheme
  change layout.scheme.key.representation.encoding.words +
    (layout.scheme.cache.lookup.table.representation.encoding.words + layout.scheme.metadata.representation.encoding.words) ≤ _
  omega

def tail : Layout w (List F × EncodedState F G M) := layout.flat.attach.values.prod layout.scheme.state
  (layout.fits_of_le (by
    have scalarLists := layout.flat.attach.base_sizes
    rw [Flatten.Layouts.attach_width] at scalarLists
    have state := layout.scheme_size
    rw [width_eq]; omega))
def rawInput : Layout w ((M × G) × List F × EncodedState F G M) := layout.scheme.key.prod layout.tail
  (layout.fits_of_le (by
    change layout.scheme.key.representation.encoding.words +
      (layout.flat.attach.values.representation.encoding.words + layout.scheme.state.representation.encoding.words) ≤ _
    have scalarLists := layout.flat.attach.base_sizes
    rw [Flatten.Layouts.attach_width] at scalarLists
    have state := layout.scheme_size
    rw [width_eq]; omega))

variable [DecidableEq M] [DecidableEq G]

def admissible (_layout : Layouts w M F G qH qS) (value : (M × G) × List F × EncodedState F G M) : Prop :=
  (cacheMap value.2.2.1 value.1).isNone = true → value.2.2.1.length ≤ qH + qS
instance (value : (M × G) × List F × EncodedState F G M) : Decidable (layout.admissible value) :=
  inferInstanceAs (Decidable (_ → _))
def input := layout.rawInput.restrict layout.admissible

abbrev Packed := layout.flat.input.Value × layout.input.Value
abbrev Flattened := layout.flat.affine.Value × layout.input.Value

def packed : Representation w layout.Packed := layout.flat.input.representation.prod layout.input.representation
  (layout.fits_of_le (by
    change layout.flat.input.representation.encoding.words + (layout.scheme.key.representation.encoding.words +
      (layout.flat.attach.values.representation.encoding.words + layout.scheme.state.representation.encoding.words)) ≤ _
    have frames := layout.flat.sizes
    have scalarLists := layout.flat.attach.base_sizes
    rw [Flatten.Layouts.attach_width] at scalarLists
    have state := layout.scheme_size
    rw [width_eq]; omega))
def flattened : Representation w layout.Flattened := layout.flat.affine.representation.prod layout.input.representation
  (layout.fits_of_le (by
    change layout.flat.affine.representation.encoding.words + (layout.scheme.key.representation.encoding.words +
      (layout.flat.attach.values.representation.encoding.words + layout.scheme.state.representation.encoding.words)) ≤ _
    have scalarLists := layout.flat.attach.base_sizes
    rw [Flatten.Layouts.attach_width] at scalarLists
    have state := layout.scheme_size
    have affine : layout.flat.affine.representation.encoding.words ≤ layout.flat.width := scalarLists.1
    rw [width_eq]; omega))

def flattenInput (value : layout.input.Value) : layout.flat.input.Value :=
  ⟨(value.val.2.2.2.1, value.val.2.1), value.property.1.2.2.2.1, value.property.1.2.1⟩
def packValue (value : layout.input.Value) : layout.Packed := (layout.flattenInput value, value)

def readValue [Zero F] (value : layout.Flattened) : (Read.input layout.scheme).Value := by
  refine ⟨(value.2.val.1, value.1.val, value.2.val.2.2),
    ⟨value.2.property.1.1, value.1.property, value.2.property.1.2.2⟩, ?_⟩
  intro missing
  change (lookupValue value.2.val.1 (0, false, value.1.val) value.2.val.2.2.1).1 = false at missing
  rw [lookupValue_cacheMap] at missing
  cases found : cacheMap value.2.val.2.2.1 value.2.val.1 with
  | none => exact value.2.property.2 (by simp only [found, Option.isNone_none])
  | some entry => simp only [found, Bool.true_eq_false] at missing

theorem sizes : layout.input.representation.encoding.words ≤ layout.width ∧
    layout.packed.encoding.words ≤ 3 * layout.width ∧
    layout.flattened.encoding.words ≤ 2 * layout.width := by
  have scalarLists := layout.flat.attach.base_sizes
  rw [Flatten.Layouts.attach_width] at scalarLists
  have frames := layout.flat.sizes
  have state := layout.scheme_size
  have affine : layout.flat.affine.representation.encoding.words ≤ layout.flat.width := scalarLists.1
  change layout.scheme.key.representation.encoding.words +
      (layout.flat.attach.values.representation.encoding.words + layout.scheme.state.representation.encoding.words) ≤ _ ∧
    layout.flat.input.representation.encoding.words + (layout.scheme.key.representation.encoding.words +
      (layout.flat.attach.values.representation.encoding.words + layout.scheme.state.representation.encoding.words)) ≤ _ ∧
    layout.flat.affine.representation.encoding.words + (layout.scheme.key.representation.encoding.words +
      (layout.flat.attach.values.representation.encoding.words + layout.scheme.state.representation.encoding.words)) ≤ _
  rw [width_eq]
  omega

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
