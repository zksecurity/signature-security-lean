import Proofs.Runtime.Caliper.SchnorrAGMReachability
import Proofs.Runtime.Caliper.UniformQuery
import Proofs.Runtime.Caliper.GuardedBranchBounds

/-! Random requests have independently bounded group/coefficient lists and a
runtime range. Neither branch needs a free cache or signing-history slot. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native

abbrev Input (M F G : Type) := List G × List (List F) × Nat × EncodedState F G M
def shape {M F G : Type} (args : Input M F G) : Bool := args.1.isEmpty

structure Layouts (w : Nat) (M F G : Type) (qH qS randomBound : Nat) where
  scheme : SchnorrAGM.Layouts w M F G qH qS
  rangeFits : randomBound + 1 ≤ 2 ^ w
  groups : Nat
  rows : Nat
  coefficients : Nat
  groupCountFits : groups < 2 ^ w
  rowCountFits : rows < 2 ^ w
  coefficientCountFits : coefficients < 2 ^ w
  storageFits : 32 * (scheme.width + (1 + groups * scheme.point.representation.encoding.words) +
    (1 + coefficients * scheme.scalar.representation.encoding.words) +
      (1 + rows * (1 + coefficients * scheme.scalar.representation.encoding.words)) + 4) < 2 ^ w

namespace Layouts
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)
def width : Nat := layout.scheme.width + (1 + layout.groups * layout.scheme.point.representation.encoding.words) +
  (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words) +
    (1 + layout.rows * (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words)) + 4
theorem fits_of_le {words : Nat} (bound : words ≤ 32 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits
theorem state_le : layout.scheme.point.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤ layout.scheme.width := by
  rw [SchnorrAGM.Layouts.state_words]
  dsimp only [SchnorrAGM.Layouts.width, storageWidth]
  omega

def points : Layout w (List G) := layout.scheme.point.boundedList layout.groups layout.groupCountFits
  (layout.fits_of_le (by unfold width; omega))
def scalarRow : Layout w (List F) := layout.scheme.scalar.boundedList layout.coefficients layout.coefficientCountFits
  (layout.fits_of_le (by unfold width; omega))
def coefficientRows : Layout w (List (List F)) := layout.scalarRow.boundedList layout.rows layout.rowCountFits
  (layout.fits_of_le (by change 1 + layout.rows * (1 + layout.coefficients * _) ≤ _; unfold width; omega))
theorem parts : layout.scheme.width + layout.points.representation.encoding.words + layout.scalarRow.representation.encoding.words +
    layout.coefficientRows.representation.encoding.words + 4 = layout.width := rfl
def counter : Layout w Nat := Layout.counter w (randomBound + 1) (width_pos layout.scheme.wordFits) layout.rangeFits
def base : Layout w (Nat × EncodedState F G M) := layout.counter.prod layout.scheme.state
  (layout.fits_of_le (by change 1 + _ ≤ _; have := layout.state_le; have := layout.parts; omega))
def tail : Layout w (List (List F) × Nat × EncodedState F G M) := layout.coefficientRows.prod layout.base
  (layout.fits_of_le (by change _ + (1 + _) ≤ _; have := layout.state_le; have := layout.parts; omega))
def input : Layout w (Input M F G) := layout.points.prod layout.tail
  (layout.fits_of_le (by change _ + (_ + (1 + _)) ≤ _; have := layout.state_le; have := layout.parts; omega))
theorem input_words : layout.input.representation.encoding.words = layout.points.representation.encoding.words +
    (layout.coefficientRows.representation.encoding.words + (1 + layout.scheme.state.representation.encoding.words)) := rfl
theorem input_le : layout.input.representation.encoding.words ≤ layout.width := by
  rw [input_words]; have := layout.parts; have := layout.state_le; omega
theorem base_le : layout.base.representation.encoding.words ≤ layout.width := by
  change 1 + _ ≤ _; have := layout.parts; have := layout.state_le; omega
theorem duplicateFits : layout.input.representation.encoding.words + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.input_le; omega)
theorem tagFits : 1 + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.input_le; have := layout.parts; omega)
theorem frameFits : 2 + layout.scheme.state.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.parts; have := layout.state_le; omega)

def replyPoints : Layout w (List G) := layout.scheme.point.boundedList 1 (by have := layout.scheme.wordFits; omega)
  (layout.fits_of_le (by have := layout.parts; have := layout.state_le; omega))
def reply : Layout w (Nat × List G) := layout.counter.prod layout.replyPoints
  (layout.fits_of_le (by change 1 + (1 + 1 * _) ≤ _; have := layout.parts; have := layout.state_le; omega))
def output : Layout w ((Nat × List G) × EncodedState F G M) := layout.reply.prod layout.scheme.state
  (layout.fits_of_le (by change (1 + (1 + 1 * _)) + _ ≤ _; have := layout.parts; have := layout.state_le; omega))
theorem output_le : layout.output.representation.encoding.words ≤ layout.width := by
  change (1 + (1 + 1 * _)) + _ ≤ _; have := layout.parts; have := layout.state_le; omega

def port := UniformQuery.port randomBound layout.scheme.wordFits layout.rangeFits
def forwarded := UniformQuery.output randomBound layout.scheme.wordFits layout.rangeFits layout.scheme.state.representation layout.frameFits
end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
