import Signatures.Runtime.Caliper.TokenEvaluationMemory
import Signatures.Runtime.Caliper.BLSRowsOracle

/-! BLS transcript evaluation shares the original scalar and pair-cache
representations. Transcript and coefficient capacities remain independent. -/
namespace Signatures.Runtime.CaliperBackend.BLSTokens
open Caliper BoundedSource
structure Layouts (w : Nat) (M G F : Type) where
  rows : BLSRows.Layouts w M G F
  capacity : Nat
  coefficients : Nat
  counterFits : capacity + 2 ≤ 2 ^ w
  coefficientCountFits : coefficients < 2 ^ w
  goodStorageFits : 16 * (4 + (capacity + 1) *
    (rows.good.token.representation.encoding.words + rows.accumulation.cache.value.representation.encoding.words) +
    (coefficients + 1) * rows.accumulation.cache.value.representation.encoding.words +
    rows.good.state.representation.encoding.words) < 2 ^ w
  badStorageFits : 16 * (4 + (capacity + 1) *
    (rows.bad.token.representation.encoding.words + rows.accumulation.cache.value.representation.encoding.words) +
    (coefficients + 1) * rows.accumulation.cache.value.representation.encoding.words +
    rows.bad.state.representation.encoding.words) < 2 ^ w
namespace Layouts
variable {w : Nat} {M G F : Type} (layout : Layouts w M G F)
def good : TokenEvaluation.Layouts w M G F F :=
  ⟨layout.rows.good, layout.capacity, layout.coefficients, layout.counterFits, layout.coefficientCountFits, layout.goodStorageFits⟩
def bad : TokenEvaluation.Layouts w M G F (F × F) :=
  ⟨layout.rows.bad, layout.capacity, layout.coefficients, layout.counterFits, layout.coefficientCountFits, layout.badStorageFits⟩
end Layouts
variable {w : Nat} {M G F : Type} [Zero F] (layout : Layouts w M G F)
    (zeroValid : layout.rows.accumulation.cache.value.valid 0)
def zero : layout.rows.accumulation.cache.value.Value := ⟨0, zeroValid⟩
def pairZero : layout.rows.bad.accumulation.cache.value.Value := ⟨(0, 0), zeroValid, zeroValid⟩
end Signatures.Runtime.CaliperBackend.BLSTokens
