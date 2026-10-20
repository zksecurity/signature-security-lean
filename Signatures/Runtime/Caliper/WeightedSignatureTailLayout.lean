import Signatures.Runtime.Caliper.WeightedExtractionMemory
import Signatures.Runtime.Caliper.WeightedTargetBounds
import Signatures.Runtime.Caliper.WeightedTargetSource

/-! A forged message and scalar numerator remain stored throughout signing
extraction. Executed swapping then assembles the target evaluator's input;
the final reassociation is justified by equality of its stored bytes. -/
namespace Signatures.Runtime.CaliperBackend.WeightedSignatureTail
open Caliper BoundedSource

variable {w : Nat} {K M G F R : Type} (layout : WeightedExtraction.Layouts w K M G F R)

def context : Layout w (M × F) :=
  layout.rows.weighted.message.prod layout.rows.accumulation.coefficient
    (layout.rows.weighted.fits (by
      have := layout.rows.accumulation.base_sizes
      unfold WeightedCoefficient.Layouts.width
      dsimp only [WeightedToken.Layouts.accumulation] at *
      omega))

theorem context_size : (context layout).representation.encoding.words ≤ 2 * layout.width := by
  have messageBound : layout.rows.weighted.message.representation.encoding.words +
      layout.rows.point.representation.encoding.words ≤ layout.assembly.width := layout.assembly.base_sizes.1
  have scalarBound : layout.rows.accumulation.coefficient.representation.encoding.words ≤
      layout.assembly.width := layout.assembly.base_sizes.2.1
  have whole := layout.base_sizes.1
  change layout.rows.weighted.message.representation.encoding.words +
    layout.rows.accumulation.coefficient.representation.encoding.words ≤ _
  omega

abbrev Input := layout.input.Value × (context layout).Value
abbrev Returned := layout.rows.state.Value × (context layout).Value
def input : Representation w (Input layout) :=
  layout.input.representation.prod (context layout).representation
    (layout.fits_of_le (by have := layout.input_size; have := context_size layout; omega))
def returned : Representation w (Returned layout) :=
  layout.rows.state.representation.prod (context layout).representation
    (layout.fits_of_le (by have := layout.base_sizes.2.1; have := context_size layout; omega))
abbrev output := WeightedTarget.output layout.rows.weighted

def argument (value : Returned layout) : layout.rows.weighted.input.Value :=
  ⟨(value.2.val.1, value.2.val.2, value.1.val), value.2.property.1, value.2.property.2, value.1.property⟩
def route : Realizer .unit (returned layout) layout.rows.weighted.input.representation (argument layout) :=
  (Pairing.swap .unit (by decide) layout.rows.state.representation (context layout).representation
    layout.rows.accumulation.cache.wordFits (returned layout).fits).viewOutput _
    (argument layout) (by
      intro value
      change _ ++ (_ ++ _) = (_ ++ _) ++ _
      exact (List.append_assoc _ _ _).symm)
theorem route_time (value : Returned layout) :
    (route layout).time value ≤ 8 * (returned layout).encoding.words :=
  Pairing.swap_time_unit_le _ _ layout.rows.accumulation.cache.wordFits (returned layout).fits value
theorem route_words : descriptionWords (route layout).code ≤ 26 * (returned layout).encoding.words + 14 :=
  Pairing.swap_descriptionWords_le .unit (by decide) _ _ layout.rows.accumulation.cache.wordFits (returned layout).fits
theorem route_buffers : (route layout).code.memBound ≤ 2 := Reorder.buffers _ _ _
theorem route_names (names : Nat) : NamesAccounted (route layout).code names := Reorder.names _ _ _ _

def ready (value : Input layout) : Prop :=
  value.1.val.2.length + layout.terms * value.1.val.1.1.length + layout.terms ≤
    layout.rows.accumulation.cache.capacityPred + 1
instance (value : Input layout) : Decidable (ready layout value) := inferInstanceAs (Decidable (_ ≤ _))
theorem signing_ready (value : Input layout) (admitted : ready layout value) : layout.ready value.1 := by
  unfold ready at admitted
  unfold WeightedExtraction.Layouts.ready
  omega

end Signatures.Runtime.CaliperBackend.WeightedSignatureTail
