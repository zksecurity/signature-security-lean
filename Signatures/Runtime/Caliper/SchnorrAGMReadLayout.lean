import Signatures.Runtime.Caliper.SchnorrAGMCache
import Signatures.Runtime.Caliper.StatefulCacheBuffers

/-! Complete Schnorr read frames. A full cache is admitted on a hit; a miss
requires a spare slot. The basis, signed messages and flags are represented
runtime data retained around the stateful cache. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

abbrev RawInput := (M × G) × (F × F) × EncodedState F G M
abbrev RawOutput := F × EncodedState F G M

theorem components :
    layout.key.representation.encoding.words + layout.entry.representation.encoding.words +
      layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words = layout.width := by
  change layout.key.representation.encoding.words + layout.entry.representation.encoding.words +
    (1 + (qH + qS + 1) * (layout.key.representation.encoding.words + layout.entry.representation.encoding.words)) +
    ((1 + (qS + 2) * layout.affine.representation.encoding.words) + ((1 + qS * _) + (1 + 1))) = _
  rw [Layouts.key_words, Layouts.entry_words, Layouts.affine_words]
  dsimp only [Layouts.width, storageWidth]
  omega

def inputTail : Layout w ((F × F) × EncodedState F G M) := layout.affine.prod layout.state
  (layout.fits_of_le (by
    change layout.affine.representation.encoding.words +
      (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words) ≤ _
    have := components layout; rw [Layouts.affine_words] at *
    have := layout.entry_words; omega))
def rawInput : Layout w (RawInput (M := M) (F := F) (G := G)) := layout.key.prod (inputTail layout)
  (layout.fits_of_le (by
    change layout.key.representation.encoding.words + (layout.affine.representation.encoding.words +
      (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words)) ≤ _
    have := components layout; have := layout.entry_words; rw [Layouts.affine_words]; omega))
def output : Layout w (RawOutput (M := M) (F := F) (G := G)) := layout.scalar.prod layout.state
  (layout.fits_of_le (by
    change layout.scalar.representation.encoding.words +
      (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words) ≤ _
    have := components layout; have := layout.entry_words; omega))

variable [Zero F] [DecidableEq M] [DecidableEq G]

def cacheInput (value : RawInput (M := M) (F := F) (G := G)) :
    CacheLayout.Input (M × G) (EncodedEntry F) :=
  (value.1, (0, false, value.2.1), value.2.2.1, ())
def input : Layout w (RawInput (M := M) (F := F) (G := G)) :=
  (rawInput layout).restrict (fun value => layout.cache.admissible (cacheInput value))

abbrev Packed := (layout.cache.input.Value × (Cache.saved layout).Value) × layout.metadata.Value
abbrev Returned := ((CacheRead.output layout.cache).Value × (Cache.saved layout).Value) × layout.metadata.Value

def packed : Representation w (Packed layout) := (Cache.model layout).input.prod layout.metadata.representation
  (layout.fits_of_le (by
    change ((layout.key.representation.encoding.words + (layout.entry.representation.encoding.words +
      (layout.cache.lookup.table.representation.encoding.words + 0))) + (layout.affine.representation.encoding.words + 1)) +
      layout.metadata.representation.encoding.words ≤ _
    have := components layout; have := layout.entry_words
    rw [Layouts.affine_words]; omega))
def returned : Representation w (Returned layout) := (Cache.model layout).output.prod layout.metadata.representation
  (layout.fits_of_le (by
    change ((layout.entry.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words) +
      (layout.affine.representation.encoding.words + 1)) + layout.metadata.representation.encoding.words ≤ _
    have := components layout; have := layout.entry_words; rw [Layouts.affine_words]; omega))

def inputKey (value : (input layout).Value) : layout.key.Value := ⟨value.val.1, value.property.1.1⟩
def inputAffine (value : (input layout).Value) : layout.affine.Value := ⟨value.val.2.1, value.property.1.2.1⟩
def inputTable (value : (input layout).Value) : layout.cache.lookup.table.Value :=
  ⟨value.val.2.2.1, value.property.1.2.2.1⟩
def inputMetadata (value : (input layout).Value) : layout.metadata.Value :=
  ⟨value.val.2.2.2, value.property.1.2.2.2⟩

def packValue (zeroValid : layout.scalar.valid 0) (value : (input layout).Value) : Packed layout :=
  ((⟨cacheInput value.val, ⟨value.property.1.1, ⟨zeroValid, trivial, value.property.1.2.1⟩,
      value.property.1.2.2.1, trivial⟩, value.property.2⟩,
    ⟨(value.val.2.1, value.val.2.2.2.2.2.2), value.property.1.2.1, trivial⟩), inputMetadata layout value)

def returnValue (value : Returned layout) : (output layout).Value :=
  ⟨(value.1.1.val.1.1, value.1.1.val.2, value.2.val.1, value.2.val.2.1, value.2.val.2.2.1, value.1.2.val.2),
    value.1.1.property.1.1, value.1.1.property.2, value.2.property.1, value.2.property.2.1, trivial, trivial⟩

theorem input_bytes (value : (input layout).Value) : (input layout).representation.encoding.encode value =
    layout.key.representation.encoding.encode (inputKey layout value) ++
      (layout.affine.representation.encoding.encode (inputAffine layout value) ++
        (layout.cache.lookup.table.representation.encoding.encode (inputTable layout value) ++
          layout.metadata.representation.encoding.encode (inputMetadata layout value))) := rfl

theorem sizes : (input layout).representation.encoding.words ≤ 2 * layout.width ∧
    (packed layout).encoding.words ≤ 3 * layout.width ∧
    (returned layout).encoding.words ≤ 3 * layout.width ∧
    (output layout).representation.encoding.words ≤ 2 * layout.width := by
  change layout.key.representation.encoding.words + (layout.affine.representation.encoding.words +
    (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words)) ≤ _ ∧
    ((layout.key.representation.encoding.words + (layout.entry.representation.encoding.words +
      (layout.cache.lookup.table.representation.encoding.words + 0))) + (layout.affine.representation.encoding.words + 1)) +
      layout.metadata.representation.encoding.words ≤ _ ∧
    ((layout.entry.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words) +
      (layout.affine.representation.encoding.words + 1)) + layout.metadata.representation.encoding.words ≤ _ ∧
    layout.scalar.representation.encoding.words +
      (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words) ≤ _
  rw [Layouts.affine_words]
  have := components layout; have := layout.entry_words
  omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
