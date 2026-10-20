import Signatures.Runtime.Caliper.SchnorrAGMSigningArithmetic
import Signatures.Runtime.Caliper.ListSnocBounds

/-! Signing history updates keep the original capacities. The temporary append
slot has its own counter bound; each admitted input reserves a basis and signed
message slot. Capacity zero therefore admits no signing history update. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native

abbrev Output (M F G : Type) := ((M × G) × EncodedEntry F × List ((M × G) × EncodedEntry F) × Unit) ×
  (G × F) × Metadata F M

structure Layouts (w : Nat) (M F G : Type) (qH qS : Nat) where
  signing : Signing.Layouts w M F G qH qS
  counterFits : qS + 3 < 2 ^ w

namespace Layouts
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)
abbrev scheme := layout.signing.scheme
def width : Nat := layout.signing.width
theorem fits_of_le {words : Nat} (bound : words ≤ 64 * layout.width) : words < 2 ^ w := layout.signing.fits_of_le bound

theorem parts : layout.scheme.basis.representation.encoding.words + layout.scheme.signed.representation.encoding.words + 2 ≤
    layout.scheme.width := by
  have parts := layout.signing.parts
  change layout.scheme.message.representation.encoding.words +
    (layout.scheme.cache.lookup.table.representation.encoding.words +
      (layout.scheme.basis.representation.encoding.words + (layout.scheme.signed.representation.encoding.words + (1 + 1)))) ≤ _ at parts
  dsimp only [scheme] at *
  omega

def basisAppend : ListSnoc.Layouts w (F × F) where
  entry := layout.scheme.affine
  capacity := qS + 2
  wordFits := layout.scheme.wordFits
  countFits := layout.counterFits
  storageFits := layout.fits_of_le (by
    have parts := layout.parts
    rw [SchnorrAGM.Layouts.basis_words, SchnorrAGM.Layouts.affine_words] at *
    dsimp only [width, Signing.Layouts.width]
    nlinarith)
def signedAppend : ListSnoc.Layouts w M where
  entry := layout.scheme.message
  capacity := qS
  wordFits := layout.scheme.wordFits
  countFits := by have := layout.counterFits; omega
  storageFits := layout.fits_of_le (by
    have parts := layout.signing.parts
    change layout.scheme.message.representation.encoding.words +
      (layout.scheme.cache.lookup.table.representation.encoding.words +
        (layout.scheme.basis.representation.encoding.words + ((1 + qS * layout.scheme.message.representation.encoding.words) + (1 + 1)))) ≤ _ at parts
    dsimp only [width, Signing.Layouts.width]
    nlinarith)

def room (_layout : Layouts w M F G qH qS) (input : Work M F G) : Prop :=
  input.2.2.2.2.1.length < qS + 2 ∧ input.2.2.2.2.2.1.length < qS
instance roomDecidable : DecidablePred (layout.room) := by intro input; unfold room; infer_instance
def input : Layout w (Work M F G) := layout.signing.work.restrict layout.room

theorem components : layout.signing.work.representation.encoding.words =
    layout.scheme.cache.lookup.input.representation.encoding.words + layout.signing.computed.representation.encoding.words +
      layout.scheme.affine.representation.encoding.words + layout.scheme.message.representation.encoding.words +
        layout.scheme.basis.representation.encoding.words + layout.scheme.signed.representation.encoding.words + 2 := by
  change _ + (_ + (_ + (_ + (_ + (_ + (1 + 1)))))) = _
  dsimp only [scheme]
  omega
theorem input_le : layout.input.representation.encoding.words ≤ 3 * layout.width := layout.signing.work_le

def saved : Layout w ((G × F) × Metadata F M) := layout.signing.computed.prod layout.scheme.metadata
  (layout.fits_of_le (by
    have := layout.signing.work_le
    rw [layout.components] at this
    change _ + (_ + (_ + (1 + 1))) ≤ _
    unfold width; omega))
def output : Layout w (Output M F G) := layout.scheme.cache.lookup.input.prod layout.saved
  (layout.fits_of_le (by
    have := layout.signing.work_le
    rw [layout.components] at this
    change _ + (_ + (_ + (_ + (1 + 1)))) ≤ _
    unfold width; omega))
theorem sizes : layout.basisAppend.input.representation.encoding.words ≤ 3 * layout.width ∧
    layout.signedAppend.input.representation.encoding.words ≤ 3 * layout.width ∧
    layout.output.representation.encoding.words ≤ 3 * layout.width := by
  have bound := layout.signing.work_le
  rw [layout.components] at bound
  change (layout.scheme.affine.representation.encoding.words + layout.scheme.basis.representation.encoding.words) ≤ _ ∧
    (layout.scheme.message.representation.encoding.words + layout.scheme.signed.representation.encoding.words) ≤ _ ∧
    (layout.scheme.cache.lookup.input.representation.encoding.words + (layout.signing.computed.representation.encoding.words +
      (layout.scheme.basis.representation.encoding.words + (layout.scheme.signed.representation.encoding.words + (1 + 1))))) ≤ _
  dsimp only [width]
  omega

theorem field_sizes : layout.scheme.cache.lookup.input.representation.encoding.words ≤ 3 * layout.width ∧
    layout.signing.computed.representation.encoding.words ≤ 3 * layout.width ∧
    layout.signing.saved.representation.encoding.words ≤ 3 * layout.width ∧
    layout.signing.history.representation.encoding.words ≤ 3 * layout.width ∧
    layout.signing.historyTail.representation.encoding.words ≤ 3 * layout.width ∧
    layout.scheme.affine.representation.encoding.words ≤ 3 * layout.width ∧
    layout.scheme.message.representation.encoding.words ≤ 3 * layout.width ∧
    layout.scheme.metadata.representation.encoding.words ≤ 3 * layout.width ∧
    layout.scheme.basis.representation.encoding.words ≤ 3 * layout.width ∧
    layout.scheme.signedFlags.representation.encoding.words ≤ 3 * layout.width ∧
    layout.scheme.signed.representation.encoding.words ≤ 3 * layout.width ∧
    layout.scheme.flags.representation.encoding.words ≤ 3 * layout.width ∧
    layout.saved.representation.encoding.words ≤ 3 * layout.width := by
  have bound := layout.signing.work_le
  rw [layout.components] at bound
  change _ ≤ _ ∧ _ ≤ _ ∧
    (_ + (_ + (_ + (_ + (_ + (1 + 1)))))) ≤ _ ∧ (_ + (_ + (_ + (_ + (1 + 1))))) ≤ _ ∧
    (_ + (_ + (_ + (1 + 1)))) ≤ _ ∧ _ ≤ _ ∧ _ ≤ _ ∧ (_ + (_ + (1 + 1))) ≤ _ ∧
    _ ≤ _ ∧ (_ + (1 + 1)) ≤ _ ∧ _ ≤ _ ∧ (1 + 1) ≤ _ ∧ (_ + (_ + (_ + (1 + 1)))) ≤ _
  dsimp only [width, scheme] at *
  omega

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Histories
