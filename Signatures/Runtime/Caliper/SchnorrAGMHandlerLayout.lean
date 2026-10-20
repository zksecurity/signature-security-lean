import Signatures.Runtime.Caliper.SchnorrAGMRandomMemory
import Signatures.Runtime.Caliper.SchnorrAGMRandomSource
import Signatures.Runtime.Caliper.SchnorrAGMHashDispatchMemory
import Signatures.Runtime.Caliper.SchnorrAGMSigningDispatchMemory
import Signatures.Runtime.Caliper.SchnorrAGMSigningDispatchSource

/-! The three handlers share one scheme store and one set of request-list
capacities. Component layouts are derived from these common parameters. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler
open Caliper BoundedSource

def storageWidth {w qH qS : Nat} {M F G : Type} (scheme : SchnorrAGM.Layouts w M F G qH qS)
    (groups rows coefficients : Nat) : Nat :=
  (scheme.width + 4 + (qS + 3) * (3 * scheme.scalar.representation.encoding.words) +
    (coefficients + 1) * scheme.scalar.representation.encoding.words) +
  (scheme.width + 2 * scheme.scalar.representation.encoding.words + 2 * scheme.point.representation.encoding.words + 1) +
  (1 + groups * scheme.point.representation.encoding.words) +
  (1 + coefficients * scheme.scalar.representation.encoding.words) +
  (1 + rows * (1 + coefficients * scheme.scalar.representation.encoding.words)) + 4

structure Layouts (w : Nat) (M F G : Type) (qH qS randomBound : Nat) where
  scheme : SchnorrAGM.Layouts w M F G qH qS
  groups : Nat
  rows : Nat
  coefficients : Nat
  rangeFits : randomBound + 1 ≤ 2 ^ w
  counterFits : qS + 4 ≤ 2 ^ w
  groupCountFits : groups < 2 ^ w
  rowCountFits : rows < 2 ^ w
  coefficientCountFits : coefficients < 2 ^ w
  storageFits : 128 * storageWidth scheme groups rows coefficients < 2 ^ w

namespace Layouts
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)
def width : Nat := storageWidth layout.scheme layout.groups layout.rows layout.coefficients
theorem fits_of_le {words : Nat} (bound : words ≤ 128 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits

abbrev hashCore : Hash.Layouts w M F G qH qS where
  scheme := layout.scheme
  coefficients := layout.coefficients
  counterFits := layout.counterFits
  coefficientCountFits := layout.coefficientCountFits
  storageFits := layout.fits_of_le (by unfold width storageWidth; omega)
abbrev arithmetic : Signing.Layouts w M F G qH qS where
  scheme := layout.scheme
  storageFits := layout.fits_of_le (by unfold width storageWidth; omega)
abbrev histories : Signing.Histories.Layouts w M F G qH qS where
  signing := layout.arithmetic
  counterFits := by have := layout.counterFits; omega
abbrev random : Random.Layouts w M F G qH qS randomBound where
  scheme := layout.scheme
  rangeFits := layout.rangeFits
  groups := layout.groups
  rows := layout.rows
  coefficients := layout.coefficients
  groupCountFits := layout.groupCountFits
  rowCountFits := layout.rowCountFits
  coefficientCountFits := layout.coefficientCountFits
  storageFits := layout.fits_of_le (by unfold width storageWidth; omega)
abbrev hash : HashDispatch.Layouts w M F G qH qS where
  hash := layout.hashCore
  groups := layout.groups
  rows := layout.rows
  groupCountFits := layout.groupCountFits
  rowCountFits := layout.rowCountFits
  storageFits := layout.fits_of_le (by
    change 32 * ((layout.scheme.width + 4 + (qS + 3) * (3 * layout.scheme.scalar.representation.encoding.words) +
      (layout.coefficients + 1) * layout.scheme.scalar.representation.encoding.words) +
        (1 + layout.groups * layout.scheme.point.representation.encoding.words) +
          (1 + layout.rows * (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words))) ≤ _
    unfold width storageWidth; omega)
abbrev signing : SigningDispatch.Layouts w M F G qH qS where
  signing := layout.histories
  groups := layout.groups
  rows := layout.rows
  coefficients := layout.coefficients
  groupCountFits := layout.groupCountFits
  rowCountFits := layout.rowCountFits
  coefficientCountFits := layout.coefficientCountFits
  storageFits := layout.fits_of_le (by
    change 32 * ((layout.scheme.width + 2 * layout.scheme.scalar.representation.encoding.words +
      2 * layout.scheme.point.representation.encoding.words + 1) +
        (1 + layout.groups * layout.scheme.point.representation.encoding.words) +
          (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words) +
            (1 + layout.rows * (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words))) ≤ _
    unfold width storageWidth; omega)

theorem core_widths : layout.random.width ≤ layout.width ∧ layout.hash.width ≤ layout.width ∧ layout.signing.width ≤ layout.width := by
  change (layout.scheme.width + (1 + layout.groups * layout.scheme.point.representation.encoding.words) +
    (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words) +
      (1 + layout.rows * (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words)) + 4 ≤ _) ∧
    ((layout.scheme.width + 4 + (qS + 3) * (3 * layout.scheme.scalar.representation.encoding.words) +
      (layout.coefficients + 1) * layout.scheme.scalar.representation.encoding.words) +
        (1 + layout.groups * layout.scheme.point.representation.encoding.words) +
          (1 + layout.rows * (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words)) ≤ _) ∧
    ((layout.scheme.width + 2 * layout.scheme.scalar.representation.encoding.words + 2 * layout.scheme.point.representation.encoding.words + 1) +
      (1 + layout.groups * layout.scheme.point.representation.encoding.words) +
        (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words) +
          (1 + layout.rows * (1 + layout.coefficients * layout.scheme.scalar.representation.encoding.words)) ≤ _)
  unfold width storageWidth
  omega
theorem config_le : layout.scheme.config.representation.encoding.words ≤ layout.width := by
  rw [SchnorrAGM.Layouts.config_words]
  unfold width storageWidth
  omega
theorem scheme_le : layout.scheme.width ≤ layout.width := by unfold width storageWidth; omega
theorem width_pos : 0 < layout.width := by unfold width storageWidth; omega
theorem state_parts : layout.scheme.message.representation.encoding.words +
    layout.scheme.state.representation.encoding.words ≤ layout.scheme.width :=
  layout.arithmetic.parts

abbrev points := layout.random.points
abbrev coefficientRows := layout.random.coefficientRows
def lists : Layout w (List G × List (List F)) := layout.points.prod layout.coefficientRows
  (layout.fits_of_le (by
    change layout.random.points.representation.encoding.words +
      layout.random.coefficientRows.representation.encoding.words ≤ _
    have := layout.random.parts; have := layout.core_widths; omega))
theorem lists_words : layout.lists.representation.encoding.words = layout.points.representation.encoding.words +
    layout.coefficientRows.representation.encoding.words := rfl
theorem lists_le : layout.lists.representation.encoding.words ≤ layout.width := by
  change layout.random.points.representation.encoding.words +
    layout.random.coefficientRows.representation.encoding.words ≤ _
  have := layout.random.parts; have := layout.core_widths; omega
def randomArgs : Layout w (Nat × List G × List (List F)) := layout.random.counter.prod layout.lists
  (layout.fits_of_le (by change 1 + _ ≤ _; have := layout.lists_le; have := layout.width_pos; omega))
def groupArgs : Layout w (M × List G × List (List F)) := layout.scheme.message.prod layout.lists
  (layout.fits_of_le (by
    have := layout.lists_le
    have := layout.state_parts
    have := layout.scheme_le
    omega))
theorem args_le : layout.randomArgs.representation.encoding.words ≤ 2 * layout.width ∧
    layout.groupArgs.representation.encoding.words ≤ 2 * layout.width := by
  change (1 + layout.lists.representation.encoding.words ≤ _) ∧
    (layout.scheme.message.representation.encoding.words + layout.lists.representation.encoding.words ≤ _)
  have := layout.lists_le
  have := layout.state_parts
  have := layout.scheme_le
  have := layout.width_pos
  omega
theorem store_le : layout.scheme.store.representation.encoding.words ≤ 2 * layout.width := by
  change layout.scheme.config.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤ _
  have := layout.config_le
  have := layout.state_parts
  have := layout.scheme_le
  omega
def randomInput : Layout w ((Nat × List G × List (List F)) × (G × G) × Signatures.Runtime.SchnorrAGM.Native.EncodedState F G M) :=
  layout.randomArgs.prod layout.scheme.store (layout.fits_of_le (by have := layout.args_le; have := layout.store_le; omega))
def groupInput : Layout w ((M × List G × List (List F)) × (G × G) × Signatures.Runtime.SchnorrAGM.Native.EncodedState F G M) :=
  layout.groupArgs.prod layout.scheme.store (layout.fits_of_le (by have := layout.args_le; have := layout.store_le; omega))
def randomOutput := layout.random.reply.prod layout.scheme.store
  (layout.fits_of_le (by
    have := layout.random.output_le
    change layout.random.reply.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤ _ at this
    have := layout.core_widths; have := layout.store_le; omega))
def scalarOutput := layout.signing.reply.prod layout.scheme.store
  (layout.fits_of_le (by
    have := layout.signing.output_le
    change layout.signing.reply.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤ _ at this
    have := layout.core_widths; have := layout.store_le; omega))

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler
