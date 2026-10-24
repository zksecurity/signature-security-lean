import Proofs.Runtime.Caliper.SchnorrAGMSamplingMemory
import Proofs.Runtime.Caliper.SchnorrAGMSamplingSource
import Proofs.Runtime.Caliper.GuardedBranchBounds

/-! Signing requests retain arbitrary represented group and coefficient lists.
Their capacities are independent, including zero. Only accepted requests need
free signing slots; malformed requests may contain full stores. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native

abbrev Input (M F G : Type) := List G × List (List F) × Signing.Sampling.RequestState M F G
def shape {M F G : Type} (args : Input M F G) : Bool := args.1.isEmpty

structure Layouts (w : Nat) (M F G : Type) (qH qS : Nat) where
  signing : Signing.Histories.Layouts w M F G qH qS
  groups : Nat
  rows : Nat
  coefficients : Nat
  groupCountFits : groups < 2 ^ w
  rowCountFits : rows < 2 ^ w
  coefficientCountFits : coefficients < 2 ^ w
  storageFits : 32 * (signing.width + (1 + groups * signing.scheme.point.representation.encoding.words) +
    (1 + coefficients * signing.scheme.scalar.representation.encoding.words) +
      (1 + rows * (1 + coefficients * signing.scheme.scalar.representation.encoding.words))) < 2 ^ w

namespace Layouts
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)
abbrev scheme := layout.signing.scheme
def width : Nat := layout.signing.width + (1 + layout.groups * layout.scheme.point.representation.encoding.words) +
  (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words) +
    (1 + layout.rows * (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words))
theorem fits_of_le {words : Nat} (bound : words ≤ 32 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits

def points : Layout w (List G) := layout.scheme.point.boundedList layout.groups layout.groupCountFits
  (layout.fits_of_le (by unfold width; omega))
def scalarRow : Layout w (List F) := layout.scheme.scalar.boundedList layout.coefficients layout.coefficientCountFits
  (layout.fits_of_le (by unfold width; omega))
def coefficientRows : Layout w (List (List F)) := layout.scalarRow.boundedList layout.rows layout.rowCountFits
  (layout.fits_of_le (by change 1 + layout.rows * (1 + layout.coefficients * _) ≤ _; unfold width; omega))
theorem parts : layout.signing.width + layout.points.representation.encoding.words + layout.scalarRow.representation.encoding.words +
    layout.coefficientRows.representation.encoding.words = layout.width := rfl
theorem base_le : layout.signing.signing.base.representation.encoding.words ≤ layout.signing.width := by
  have bound := layout.signing.signing.input_le
  change layout.scheme.affine.representation.encoding.words + layout.signing.signing.base.representation.encoding.words ≤ _ at bound
  exact (Nat.le_add_left _ _).trans bound

def tail : Layout w (List (List F) × Signing.Sampling.RequestState M F G) :=
  layout.coefficientRows.prod layout.signing.signing.base
    (layout.fits_of_le (by have := layout.parts; have := layout.base_le; omega))
def raw : Layout w (Input M F G) := layout.points.prod layout.tail
  (layout.fits_of_le (by
    change _ + (_ + _) ≤ _
    have := layout.parts; have := layout.base_le; omega))
def admissible (args : Input M F G) : Prop := shape args = true → Signing.Sampling.ready layout.signing args.2.2
instance admissibleDecidable : DecidablePred (layout.admissible) := by intro args; unfold admissible; infer_instance
def input : Layout w (Input M F G) := layout.raw.restrict layout.admissible
def yes := GuardedBranch.yesInput layout.input shape
def no := GuardedBranch.noInput layout.input shape
theorem input_words : layout.input.representation.encoding.words = layout.points.representation.encoding.words +
    (layout.coefficientRows.representation.encoding.words + layout.signing.signing.base.representation.encoding.words) := rfl
theorem input_le : layout.input.representation.encoding.words ≤ layout.width := by
  rw [input_words]; have := layout.parts; have := layout.base_le; omega
theorem duplicateFits : layout.input.representation.encoding.words + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.input_le; omega)
theorem tagFits : 1 + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by
    have := layout.input_le
    have positive : 0 < layout.width := by unfold width; omega
    omega)
def selected := layout.yes.sum layout.no (width_pos layout.scheme.wordFits) (by
  change 1 + max layout.input.representation.encoding.words layout.input.representation.encoding.words < 2 ^ w
  simpa only [Nat.max_self] using layout.tagFits)
def acceptedValue (args : layout.yes.Value) : (Signing.Sampling.input layout.signing).Value :=
  ⟨args.val.2.2, args.property.1.1.2.2, args.property.1.2 args.property.2⟩

def replyPoints : Layout w (List G) := layout.scheme.point.boundedList 1 (by have := layout.scheme.wordFits; omega)
  (layout.fits_of_le (by
    have := layout.parts
    dsimp only [Signing.Histories.Layouts.width, Signing.Layouts.width] at this
    change 1 + 1 * layout.scheme.point.representation.encoding.words ≤ _
    dsimp only [scheme, Signing.Histories.Layouts.scheme] at *
    omega))
def reply : Layout w (F × List G) := layout.scheme.scalar.prod layout.replyPoints
  (layout.fits_of_le (by
    have := layout.parts
    dsimp only [Signing.Histories.Layouts.width, Signing.Layouts.width] at this
    change _ + (1 + 1 * _) ≤ _
    dsimp only [scheme, Signing.Histories.Layouts.scheme] at *
    omega))
theorem output_width : (layout.scheme.scalar.representation.encoding.words + (1 + layout.scheme.point.representation.encoding.words)) +
    layout.scheme.state.representation.encoding.words ≤ layout.width := by
  have base := layout.base_le
  change layout.scheme.point.representation.encoding.words + (layout.scheme.point.representation.encoding.words +
    (layout.scheme.message.representation.encoding.words + layout.scheme.state.representation.encoding.words)) ≤ _ at base
  have input := layout.signing.signing.input_le
  rw [Signing.Layouts.input_words] at input
  have parts := layout.parts
  have rowPositive : 1 ≤ layout.scalarRow.representation.encoding.words := by change 1 ≤ 1 + _; omega
  dsimp only [scheme, Signing.Histories.Layouts.scheme, Signing.Histories.Layouts.width] at *
  omega
def output : Layout w ((F × List G) × EncodedState F G M) := layout.reply.prod layout.scheme.state
  (layout.fits_of_le (by
    have := layout.output_width
    change (_ + (1 + 1 * _)) + _ ≤ _
    omega))
theorem output_le : layout.output.representation.encoding.words ≤ layout.width := by
  change (_ + (1 + 1 * _)) + _ ≤ _
  simpa only [Nat.one_mul] using layout.output_width

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.SigningDispatch
