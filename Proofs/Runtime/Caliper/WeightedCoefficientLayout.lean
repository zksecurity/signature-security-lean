import Proofs.Runtime.Caliper.GeneratedWeightedOracle
import Proofs.Runtime.Caliper.ByteRoute

/-! A message, its chronological extraction coefficient, and the current
accumulator/cache. The existing accumulator finisher also handles a complete
message evaluation; no expanded weighted list needs to be stored. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCoefficient
open Caliper BoundedSource

structure Layouts (w : Nat) (K M F R : Type) where
  evaluation : CacheAccumulate.Layouts w K F R
  message : Layout w M
  storageFits : 16 * (message.representation.encoding.words + evaluation.width) < 2 ^ w

namespace Layouts
variable {w : Nat} {K M F R : Type} (layout : Layouts w K M F R)

def width := layout.message.representation.encoding.words + layout.evaluation.width
theorem fits {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

abbrev state := (WeightedRows.rows layout.evaluation).state
def weightedState := layout.evaluation.coefficient.prod layout.state (layout.fits (by
  change _ + (_ + _) ≤ _
  dsimp only [WeightedRows.rows]
  have := layout.evaluation.base_sizes
  unfold width
  omega))
def input := layout.message.prod layout.weightedState (layout.fits (by
  change _ + (_ + (_ + _)) ≤ _
  dsimp only [WeightedRows.rows]
  have := layout.evaluation.base_sizes
  unfold width
  omega))
def evaluationInput := layout.message.representation.prod layout.state.representation (layout.fits (by
  change _ + (_ + _) ≤ _
  dsimp only [WeightedRows.rows]
  have := layout.evaluation.base_sizes
  unfold width
  omega))
def prepared := layout.evaluationInput.prod layout.evaluation.saved.representation (layout.fits (by
  change (_ + (_ + _)) + (_ + _) ≤ _
  dsimp only [WeightedRows.rows]
  have := layout.evaluation.base_sizes
  unfold width
  omega))
abbrev post := layout.evaluation.returned

end Layouts

variable {w : Nat} {K M F R : Type} (layout : Layouts w K M F R)
def message (value : layout.input.Value) : layout.message.Value := ⟨value.val.1, value.property.1⟩
def saved (value : layout.input.Value) : layout.evaluation.saved.Value :=
  ⟨(value.val.2.1, value.val.2.2.1), value.property.2.1, value.property.2.2.1⟩
def cache (value : layout.input.Value) : layout.evaluation.cache.lookup.table.Value :=
  ⟨value.val.2.2.2, value.property.2.2.2⟩
def argument (zero : layout.evaluation.cache.value.Value) (value : layout.input.Value) :
    layout.message.Value × layout.state.Value :=
  (message layout value, ⟨(zero.val, (cache layout value).val), zero.property, (cache layout value).property⟩)
def prepareValue (zero : layout.evaluation.cache.value.Value) (value : layout.input.Value) :=
  (argument layout zero value, saved layout value)

end Signatures.Runtime.CaliperBackend.WeightedCoefficient
