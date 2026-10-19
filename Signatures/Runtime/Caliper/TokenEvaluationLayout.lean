import Signatures.Runtime.Caliper.TokenRowsSource
import Signatures.Runtime.Caliper.RowFoldPostcondition

/-! A complete transcript evaluator starts from stored tokens, coefficients
and a private cache. Token and coefficient capacities are independent. All
temporary row storage and the retained accumulator/cache fit the same word width. -/
namespace Signatures.Runtime.CaliperBackend.TokenEvaluation
open Caliper BoundedSource

structure Layouts (w : Nat) (K G F R : Type) where
  rows : RowRequest.Layouts w K G F R
  capacity : Nat
  coefficients : Nat
  counterFits : capacity + 2 ≤ 2 ^ w
  coefficientCountFits : coefficients < 2 ^ w
  storageFits : 16 * (4 + (capacity + 1) *
    (rows.token.representation.encoding.words + rows.accumulation.coefficient.representation.encoding.words) +
    (coefficients + 1) * rows.accumulation.coefficient.representation.encoding.words +
    rows.state.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {K G F R : Type} (layout : Layouts w K G F R)
def width : Nat := 4 + (layout.capacity + 1) *
    (layout.rows.token.representation.encoding.words + layout.rows.accumulation.coefficient.representation.encoding.words) +
    (layout.coefficients + 1) * layout.rows.accumulation.coefficient.representation.encoding.words +
    layout.rows.state.representation.encoding.words
theorem fits_of_le {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits
def assembly : AttachRows.Layouts w (K × G) F where
  key := layout.rows.token
  value := layout.rows.accumulation.coefficient
  capacity := layout.capacity
  coefficients := layout.coefficients
  wordFits := layout.rows.accumulation.cache.wordFits
  counterFits := layout.counterFits
  coefficientCountFits := layout.coefficientCountFits
  storageFits := layout.fits_of_le (by dsimp only [width]; omega)
theorem width_eq : layout.width = layout.assembly.width + layout.rows.state.representation.encoding.words := rfl
theorem countFits : layout.capacity < 2 ^ w := by have := layout.counterFits; omega
theorem base_sizes : layout.assembly.width ≤ layout.width ∧
    layout.rows.state.representation.encoding.words ≤ layout.width ∧
    layout.rows.accumulation.cache.lookup.table.representation.encoding.words ≤ layout.width ∧
    layout.rows.accumulation.cache.value.representation.encoding.words ≤ layout.width ∧
    layout.assembly.output.representation.encoding.words ≤ layout.width := by
  have := layout.assembly.stage_sizes (Fin.last layout.capacity)
  rw [width_eq, RowRequest.Layouts.state_words]
  change _ ∧ _ ∧ _ ∧ _ ∧ (layout.assembly.rows (Fin.last layout.capacity)).representation.encoding.words ≤ _
  omega
abbrev input : Layout w ((List (K × G) × List F) × List (K × R)) :=
  (TokenRows.input layout.assembly).prod layout.rows.accumulation.cache.lookup.table
    (layout.fits_of_le (by have := TokenRows.input_size layout.assembly; have := layout.base_sizes; omega))
abbrev prepared : Layout w (List ((K × G) × F) × (R × List (K × R))) :=
  layout.assembly.output.prod layout.rows.state
    (layout.fits_of_le (by have := layout.base_sizes; omega))
theorem input_size : layout.input.representation.encoding.words ≤ 3 * layout.width := by
  change (TokenRows.input layout.assembly).representation.encoding.words + _ ≤ _
  have := TokenRows.input_size layout.assembly
  have := layout.base_sizes
  omega
theorem prepared_size : layout.prepared.representation.encoding.words ≤ 2 * layout.width := by
  change layout.assembly.output.representation.encoding.words + _ ≤ _
  have := layout.base_sizes
  omega
theorem foldFits : 1 + layout.capacity * layout.rows.row.representation.encoding.words + layout.rows.state.representation.encoding.words < 2 ^ w :=
  layout.prepared.representation.fits
def ready (value : layout.input.Value) : Prop :=
  value.val.2.length + value.val.1.1.length ≤ layout.rows.accumulation.cache.capacityPred + 1
instance (value : layout.input.Value) : Decidable (layout.ready value) := inferInstanceAs (Decidable (_ ≤ _))
end Layouts
end Signatures.Runtime.CaliperBackend.TokenEvaluation
