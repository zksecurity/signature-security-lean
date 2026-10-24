import Proofs.Runtime.Caliper.SchnorrAGMHashMemory
import Proofs.Runtime.Caliper.GuardedBranchBounds

/-! Frames for arbitrary hash-request shapes. The point-list and row-list
capacities are independent, including zero. Only a singleton/singleton request
needs the cache admission invariant; rejected requests need no spare slot. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
open Caliper BoundedSource
open Signatures.Runtime.SchnorrAGM.Native

abbrev Input (M F G : Type) := M × List G × List (List F) × EncodedState F G M

def shape {M F G : Type} (value : Input M F G) : Bool :=
  decide (value.2.1.length = 1 ∧ value.2.2.1.length = 1)

structure Layouts (w : Nat) (M F G : Type) (qH qS : Nat) where
  hash : Hash.Layouts w M F G qH qS
  groups : Nat
  rows : Nat
  groupCountFits : groups < 2 ^ w
  rowCountFits : rows < 2 ^ w
  storageFits : 32 * (hash.width + (1 + groups * hash.scheme.point.representation.encoding.words) +
    (1 + rows * hash.flat.attach.values.representation.encoding.words)) < 2 ^ w

namespace Layouts
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def width : Nat := layout.hash.width + (1 + layout.groups * layout.hash.scheme.point.representation.encoding.words) +
  (1 + layout.rows * layout.hash.flat.attach.values.representation.encoding.words)
theorem fits_of_le {words : Nat} (bound : words ≤ 32 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def points : Layout w (List G) := layout.hash.scheme.point.boundedList layout.groups layout.groupCountFits
  (layout.fits_of_le (by unfold width; omega))
def coefficients : Layout w (List (List F)) := layout.hash.flat.attach.values.boundedList layout.rows layout.rowCountFits
  (layout.fits_of_le (by unfold width; omega))

theorem parts : layout.hash.width + layout.points.representation.encoding.words +
    layout.coefficients.representation.encoding.words = layout.width := rfl
theorem scheme_le : layout.hash.scheme.message.representation.encoding.words +
    layout.hash.scheme.state.representation.encoding.words ≤ layout.hash.width := by
  have bound := layout.hash.scheme_size
  have widths := layout.hash.width_eq
  change layout.hash.scheme.message.representation.encoding.words + layout.hash.scheme.point.representation.encoding.words +
    layout.hash.scheme.state.representation.encoding.words ≤ layout.hash.scheme.width at bound
  omega

def tail : Layout w (List (List F) × EncodedState F G M) := layout.coefficients.prod layout.hash.scheme.state
  (layout.fits_of_le (by have := layout.parts; have := layout.scheme_le; omega))
def lists : Layout w (List G × List (List F) × EncodedState F G M) := layout.points.prod layout.tail
  (layout.fits_of_le (by
    change layout.points.representation.encoding.words + (layout.coefficients.representation.encoding.words +
      layout.hash.scheme.state.representation.encoding.words) ≤ _
    have := layout.parts; have := layout.scheme_le; omega))
def raw : Layout w (Input M F G) := layout.hash.scheme.message.prod layout.lists
  (layout.fits_of_le (by
    change layout.hash.scheme.message.representation.encoding.words + (layout.points.representation.encoding.words +
      (layout.coefficients.representation.encoding.words + layout.hash.scheme.state.representation.encoding.words)) ≤ _
    have := layout.parts; have := layout.scheme_le; omega))

variable [DecidableEq M] [DecidableEq G]

def admissible (value : Input M F G) : Prop :=
  match value.2.1, value.2.2.1 with
  | [point], [coefficients] => layout.hash.admissible ((value.1, point), coefficients, value.2.2.2)
  | _, _ => True
instance (value : Input M F G) : Decidable (layout.admissible value) := by
  unfold admissible
  split <;> infer_instance
def input := layout.raw.restrict layout.admissible
def yes := GuardedBranch.yesInput layout.input shape
def no := GuardedBranch.noInput layout.input shape

theorem input_words : layout.input.representation.encoding.words =
    layout.hash.scheme.message.representation.encoding.words + (layout.points.representation.encoding.words +
      (layout.coefficients.representation.encoding.words + layout.hash.scheme.state.representation.encoding.words)) := rfl
theorem input_le : layout.input.representation.encoding.words ≤ layout.width := by
  rw [input_words]
  have := layout.parts; have := layout.scheme_le; omega
theorem duplicateFits : layout.input.representation.encoding.words + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.input_le; omega)
theorem tagFits : 1 + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by
    have := layout.input_le
    have positive : 0 < layout.width := by unfold width; omega
    omega)
def selected := layout.yes.sum layout.no (width_pos layout.hash.scheme.wordFits) (by
  change 1 + max layout.input.representation.encoding.words layout.input.representation.encoding.words < _
  simpa only [Nat.max_self] using layout.tagFits)

theorem lengths (value : layout.yes.Value) : value.val.2.1.length = 1 ∧ value.val.2.2.1.length = 1 :=
  of_decide_eq_true value.property.2
def point (value : layout.yes.Value) : G := value.val.2.1[0]'(by have := layout.lengths value; omega)
def row (value : layout.yes.Value) : List F := value.val.2.2.1[0]'(by have := layout.lengths value; omega)

theorem points_singleton (value : layout.yes.Value) : value.val.2.1 = [layout.point value] := by
  obtain ⟨head, same⟩ := List.length_eq_one_iff.mp (layout.lengths value).1
  simp only [point, same, List.getElem_cons_zero]
theorem rows_singleton (value : layout.yes.Value) : value.val.2.2.1 = [layout.row value] := by
  obtain ⟨head, same⟩ := List.length_eq_one_iff.mp (layout.lengths value).2
  simp only [row, same, List.getElem_cons_zero]

def acceptedValue (value : layout.yes.Value) : layout.hash.input.Value := by
  refine ⟨((value.val.1, layout.point value), layout.row value, value.val.2.2.2), ?_, ?_⟩
  · exact ⟨⟨value.property.1.1.1, value.property.1.1.2.1.2 _ (List.getElem_mem _)⟩,
      value.property.1.1.2.2.1.2 _ (List.getElem_mem _), value.property.1.1.2.2.2⟩
  · have admitted := value.property.1.2
    change layout.admissible value.val at admitted
    unfold admissible at admitted
    rw [layout.points_singleton value, layout.rows_singleton value] at admitted
    exact admitted

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
