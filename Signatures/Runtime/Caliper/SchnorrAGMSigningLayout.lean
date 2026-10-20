import Signatures.Runtime.Caliper.SchnorrAGMReadLayout
import Signatures.Runtime.Caliper.BLSResponseNames

/-! Signing frames keep the sampled scalars, challenge points, message and
complete source state as represented runtime data. Arithmetic produces the
original cache-programming and history-update frame without changing capacities. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native

abbrev Input (M F G : Type) := (F × F) × G × G × M × EncodedState F G M
abbrev Work (M F G : Type) := ((M × G) × EncodedEntry F × List ((M × G) × EncodedEntry F) × Unit) ×
  (G × F) × (F × F) × M × Metadata F M

structure Layouts (w : Nat) (M F G : Type) (qH qS : Nat) where
  scheme : SchnorrAGM.Layouts w M F G qH qS
  storageFits : 64 * (scheme.width + 2 * scheme.scalar.representation.encoding.words +
    2 * scheme.point.representation.encoding.words + 1) < 2 ^ w

namespace Layouts
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def width : Nat := layout.scheme.width + 2 * layout.scheme.scalar.representation.encoding.words +
  2 * layout.scheme.point.representation.encoding.words + 1
theorem fits_of_le {words : Nat} (bound : words ≤ 64 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits
theorem parts : layout.scheme.message.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤
    layout.scheme.width := by
  have parts := Read.components layout.scheme
  change layout.scheme.message.representation.encoding.words +
    (layout.scheme.cache.lookup.table.representation.encoding.words + layout.scheme.metadata.representation.encoding.words) ≤ _
  change (layout.scheme.message.representation.encoding.words + layout.scheme.point.representation.encoding.words) +
    layout.scheme.entry.representation.encoding.words + layout.scheme.cache.lookup.table.representation.encoding.words +
      layout.scheme.metadata.representation.encoding.words = _ at parts
  omega

theorem cache_width : layout.scheme.cache.lookup.width = layout.scheme.key.representation.encoding.words +
    layout.scheme.entry.representation.encoding.words + layout.scheme.cache.lookup.table.representation.encoding.words := by
  rw [LookupLayout.table_words]
  dsimp only [LookupLayout.width, CacheLayout.lookup]
  change (1 + (qH + qS + 1) * (layout.scheme.key.representation.encoding.words + layout.scheme.entry.representation.encoding.words)) +
    layout.scheme.key.representation.encoding.words + layout.scheme.entry.representation.encoding.words =
      layout.scheme.key.representation.encoding.words + layout.scheme.entry.representation.encoding.words +
        (1 + (qH + qS + 1) * (layout.scheme.key.representation.encoding.words + layout.scheme.entry.representation.encoding.words))
  omega

def arithmetic : BLSResponse.Layouts w F G where
  scalar := layout.scheme.scalar
  point := layout.scheme.point
  wordFits := layout.scheme.wordFits
  storageFits := layout.fits_of_le (by unfold width; omega)

def messageState : Layout w (M × EncodedState F G M) := layout.scheme.message.prod layout.scheme.state
  (layout.fits_of_le (by have := layout.parts; unfold width; omega))
def publicInput : Layout w (G × M × EncodedState F G M) := layout.scheme.point.prod layout.messageState
  (layout.fits_of_le (by
    change _ + (_ + _) ≤ _
    have := layout.parts; unfold width; omega))
def base : Layout w (G × G × M × EncodedState F G M) := layout.scheme.point.prod layout.publicInput
  (layout.fits_of_le (by
    change _ + (_ + (_ + _)) ≤ _
    have := layout.parts; unfold width; omega))
def input : Layout w (Input M F G) := layout.scheme.affine.prod layout.base
  (layout.fits_of_le (by
    change (_ + _) + (_ + (_ + (_ + _))) ≤ _
    have := layout.parts; unfold width; omega))
theorem input_words : layout.input.representation.encoding.words = 2 * layout.scheme.scalar.representation.encoding.words +
    2 * layout.scheme.point.representation.encoding.words +
      layout.scheme.message.representation.encoding.words + layout.scheme.state.representation.encoding.words := by
  change (_ + _) + (_ + (_ + (_ + _))) = _; omega
theorem input_le : layout.input.representation.encoding.words ≤ layout.width := by
  rw [input_words]; have := layout.parts; unfold width; omega

def computed : Layout w (G × F) := layout.scheme.point.prod layout.scheme.scalar
  (layout.fits_of_le (by unfold width; omega))
def duplicated : Representation w (layout.input.Value × layout.input.Value) := layout.input.representation.prod layout.input.representation
  (layout.fits_of_le (by have := layout.input_le; omega))
def frame : Representation w (layout.computed.Value × layout.input.Value) := layout.computed.representation.prod layout.input.representation
  (layout.fits_of_le (by
    change (_ + _) + _ ≤ _
    have := layout.input_le; unfold width at *; omega))

def historyTail : Layout w (M × Metadata F M) := layout.scheme.message.prod layout.scheme.metadata
  (layout.fits_of_le (by
    have := layout.parts
    change _ + (layout.scheme.cache.lookup.table.representation.encoding.words + layout.scheme.metadata.representation.encoding.words) ≤ _ at this
    unfold width; omega))
def history : Layout w ((F × F) × M × Metadata F M) := layout.scheme.affine.prod layout.historyTail
  (layout.fits_of_le (by
    have := layout.parts
    change _ + (layout.scheme.cache.lookup.table.representation.encoding.words + layout.scheme.metadata.representation.encoding.words) ≤ _ at this
    change (_ + _) + (_ + _) ≤ _
    unfold width; omega))
def saved : Layout w ((G × F) × (F × F) × M × Metadata F M) := layout.computed.prod layout.history
  (layout.fits_of_le (by
    have := layout.parts
    change _ + (layout.scheme.cache.lookup.table.representation.encoding.words + layout.scheme.metadata.representation.encoding.words) ≤ _ at this
    change (_ + _) + ((_ + _) + (_ + _)) ≤ _
    unfold width; omega))
def work : Layout w (Work M F G) := layout.scheme.cache.lookup.input.prod layout.saved
  (layout.fits_of_le (by
    have parts := Read.components layout.scheme
    change layout.scheme.cache.lookup.input.representation.encoding.words + ((_ + _) + ((_ + _) + (_ + _))) ≤ _
    rw [LookupLayout.input_words, layout.cache_width]
    have := layout.parts
    unfold width; omega))

theorem work_le : layout.work.representation.encoding.words ≤ 3 * layout.width := by
  have parts := Read.components layout.scheme
  have state := layout.parts
  change layout.scheme.cache.lookup.input.representation.encoding.words +
    ((layout.scheme.point.representation.encoding.words + layout.scheme.scalar.representation.encoding.words) +
      (layout.scheme.affine.representation.encoding.words +
        (layout.scheme.message.representation.encoding.words + layout.scheme.metadata.representation.encoding.words))) ≤ _
  rw [LookupLayout.input_words, SchnorrAGM.Layouts.affine_words, layout.cache_width]
  unfold width; omega

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing
