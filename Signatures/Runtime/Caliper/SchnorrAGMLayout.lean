import Signatures.Runtime.Caliper.CacheLayout
import Signatures.Runtime.Caliper.Boolean
import Signatures.Runtime.SchnorrAGMEncoding

/-! Fixed-capacity word layouts for the single-pass Schnorr AGM reduction.
The cache stores encountered message/commitment pairs, including the final
target. Its capacities depend on query allowances, never domain cardinalities.
The original tuple representation is retained for the executable handlers. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native

def storageWidth (scalar point message qH qS : Nat) : Nat :=
  message + point + (3 * scalar + 1) +
    (1 + (qH + qS + 1) * (message + point + (3 * scalar + 1))) +
    (1 + (qS + 2) * (2 * scalar)) + (1 + qS * message) + 2

structure Layouts (w : Nat) (M F G : Type) (qH qS : Nat) where
  scalar : Layout w F
  point : Layout w G
  message : Layout w M
  wordFits : 16 < 2 ^ w
  countFits : qH + qS + 2 < 2 ^ w
  storageFits : 16 * storageWidth scalar.representation.encoding.words
    point.representation.encoding.words message.representation.encoding.words qH qS < 2 ^ w

namespace Layouts
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def width : Nat := storageWidth layout.scalar.representation.encoding.words
  layout.point.representation.encoding.words layout.message.representation.encoding.words qH qS

theorem fits_of_le {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def boolean : Layout w Bool := Layout.all (Representation.boolean w (width_pos layout.wordFits))
def affine : Layout w (F × F) := layout.scalar.prod layout.scalar
  (layout.fits_of_le (by dsimp only [width, storageWidth]; omega))
def optionalAffine : Layout w (Bool × F × F) := layout.boolean.prod layout.affine
  (layout.fits_of_le (by change 1 + (_ + _) ≤ _; dsimp only [width, storageWidth]; omega))
def entry : Layout w (EncodedEntry F) := layout.scalar.prod layout.optionalAffine
  (layout.fits_of_le (by change _ + (1 + (_ + _)) ≤ _; dsimp only [width, storageWidth]; omega))
def key : Layout w (M × G) := layout.message.prod layout.point
  (layout.fits_of_le (by dsimp only [width, storageWidth]; omega))

@[simp] theorem affine_words : layout.affine.representation.encoding.words =
    2 * layout.scalar.representation.encoding.words := by change _ + _ = _; omega
@[simp] theorem entry_words : layout.entry.representation.encoding.words =
    3 * layout.scalar.representation.encoding.words + 1 := by change _ + (1 + (_ + _)) = _; omega
@[simp] theorem key_words : layout.key.representation.encoding.words =
    layout.message.representation.encoding.words + layout.point.representation.encoding.words := rfl

def cache : CacheLayout w (M × G) (EncodedEntry F) where
  key := layout.key
  value := layout.entry
  capacityPred := qH + qS
  wordFits := layout.wordFits
  countFits := by have := layout.countFits; omega
  storageFits := layout.fits_of_le (by
    rw [key_words, entry_words]
    dsimp only [width, storageWidth]
    omega)

def basis : Layout w (List (F × F)) := layout.affine.boundedList (qS + 2)
  (by have := layout.countFits; omega)
  (layout.fits_of_le (by rw [affine_words]; dsimp only [width, storageWidth]; omega))
def signed : Layout w (List M) := layout.message.boundedList qS
  (by have := layout.countFits; omega)
  (layout.fits_of_le (by dsimp only [width, storageWidth]; omega))
def flags : Layout w (Bool × Bool) := layout.boolean.prod layout.boolean
  (by change 1 + 1 < _; have := layout.wordFits; omega)
def signedFlags : Layout w (List M × Bool × Bool) := layout.signed.prod layout.flags
  (layout.fits_of_le (by change (1 + qS * _) + (1 + 1) ≤ _; dsimp only [width, storageWidth]; omega))
def metadata : Layout w (Metadata F M) := layout.basis.prod layout.signedFlags
  (layout.fits_of_le (by
    change (1 + (qS + 2) * layout.affine.representation.encoding.words) + ((1 + qS * _) + (1 + 1)) ≤ _
    rw [affine_words]; dsimp only [width, storageWidth]; omega))
def state : Layout w (EncodedState F G M) := layout.cache.lookup.table.prod layout.metadata
  (layout.fits_of_le (by
    change (1 + (qH + qS + 1) * (layout.key.representation.encoding.words + layout.entry.representation.encoding.words)) +
      ((1 + (qS + 2) * layout.affine.representation.encoding.words) + ((1 + qS * _) + (1 + 1))) ≤ _
    rw [key_words, entry_words, affine_words]; dsimp only [width, storageWidth]; omega))
def config : Layout w (G × G) := layout.point.prod layout.point
  (layout.fits_of_le (by dsimp only [width, storageWidth]; omega))

@[simp] theorem basis_words : layout.basis.representation.encoding.words =
    1 + (qS + 2) * (2 * layout.scalar.representation.encoding.words) := by
  change 1 + _ * layout.affine.representation.encoding.words = _; rw [affine_words]
@[simp] theorem signed_words : layout.signed.representation.encoding.words =
    1 + qS * layout.message.representation.encoding.words := rfl
@[simp] theorem state_words : layout.state.representation.encoding.words =
    (1 + (qH + qS + 1) * (layout.message.representation.encoding.words +
      layout.point.representation.encoding.words + (3 * layout.scalar.representation.encoding.words + 1))) +
    (1 + (qS + 2) * (2 * layout.scalar.representation.encoding.words)) +
    (1 + qS * layout.message.representation.encoding.words) + 2 := by
  change (1 + (qH + qS + 1) * (layout.key.representation.encoding.words + layout.entry.representation.encoding.words)) +
    ((1 + (qS + 2) * layout.affine.representation.encoding.words) + ((1 + qS * _) + (1 + 1))) = _
  rw [key_words, entry_words, affine_words]; omega
@[simp] theorem config_words : layout.config.representation.encoding.words =
    2 * layout.point.representation.encoding.words := by change _ + _ = _; omega

def store : Layout w ((G × G) × EncodedState F G M) := layout.config.prod layout.state
  (layout.fits_of_le (by rw [config_words, state_words]; dsimp only [width, storageWidth]; omega))
def initialized : Layout w ((G × G) × (G × G) × EncodedState F G M) := layout.config.prod layout.store
  (layout.fits_of_le (by
    change layout.config.representation.encoding.words + (layout.config.representation.encoding.words + layout.state.representation.encoding.words) ≤ _
    rw [config_words, state_words]; dsimp only [width, storageWidth]; omega))

@[simp] theorem initialized_words : layout.initialized.representation.encoding.words =
    4 * layout.point.representation.encoding.words + layout.state.representation.encoding.words := by
  change layout.config.representation.encoding.words + (layout.config.representation.encoding.words + _) = _
  rw [config_words]; omega

/-- Only the scalar and point domains are required to be total. Message values
remain restricted, so an infinite mathematical message type is supported. -/
theorem encoded_valid [Field F]
    (scalars : ∀ value, layout.scalar.valid value) (points : ∀ value, layout.point.valid value)
    (s : Signatures.Runtime.SchnorrAGM.State F G M)
    (cacheLength : s.cache.length ≤ qH + qS + 1)
    (basisLength : s.representations.length ≤ qS + 2) (signedLength : s.signed.length ≤ qS)
    (cacheMessages : ∀ item ∈ s.cache, layout.message.valid item.1.1)
    (signedMessages : ∀ item ∈ s.signed, layout.message.valid item) :
    layout.state.valid (encodeState s) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨signedLength, signedMessages⟩, trivial, trivial⟩
  · change (s.cache.map (Prod.map id encodeEntry)).length ≤ qH + qS + 1
    simpa only [List.length_map] using cacheLength
  · intro item member
    change item ∈ s.cache.map (Prod.map id encodeEntry) at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact ⟨⟨cacheMessages original originalMember, points _⟩, scalars _, trivial, scalars _, scalars _⟩
  · simpa only [encodeState, encodeMetadata, List.length_map] using basisLength
  · intro item member
    change item ∈ s.representations.map encodeAffine at member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    exact ⟨scalars _, scalars _⟩

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM
