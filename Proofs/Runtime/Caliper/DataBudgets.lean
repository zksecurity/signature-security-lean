import Proofs.Runtime.Caliper.StructuralBudgets
import Proofs.Runtime.Caliper.ScalarBounds

/-! Uniform budgets for source literals, domain views and list storage. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper

variable {w : Nat} {A B : Type}

theorem Implementation.identity_boundedBy (input : Layout w A) (hw : 0 < w) :
    (Implementation.identity (cost := .unit) input hw).BoundedBy 0 1 :=
  ⟨fun _ => le_rfl, le_rfl⟩

theorem Implementation.view_boundedBy {input output : Layout w A} (hw : 0 < w)
    (preserves : ∀ value, input.valid value → output.valid value)
    (sameBytes : ∀ value : input.Value,
      output.representation.encoding.encode ⟨value.val, preserves value.val value.property⟩ = input.representation.encoding.encode value) :
    (Implementation.view (cost := .unit) hw preserves sameBytes).BoundedBy 0 1 :=
  ⟨fun _ => le_rfl, le_rfl⟩

theorem Implementation.BoundedBy.castFunction {cost : CostModel} {input : Layout w A} {output : Layout w B}
    {f g : A → B} {implementation : Implementation cost input output f} {time words : Nat}
    (bound : implementation.BoundedBy time words) (equal : f = g) :
    (implementation.castFunction equal).BoundedBy time words := ⟨bound.time_le, bound.code_le⟩

theorem DataImplementation.unit_boundedBy (input : Layout w A) (hw : 16 < 2 ^ w) :
    (DataImplementation.unit .unit (by decide) input hw).BoundedBy 0 14 :=
  ⟨fun _ => le_rfl, le_rfl⟩

theorem DataImplementation.boolean_boundedBy (input : Layout w A) (value : Bool) (hw : 16 < 2 ^ w) :
    (DataImplementation.boolean .unit (by decide) input value hw).BoundedBy 7 35 :=
  ⟨fun _ => le_rfl, le_rfl⟩

theorem DataImplementation.select_boundedBy (payload : Layout w A) (hw : 16 < 2 ^ w)
    (fits : 1 + payload.representation.encoding.words < 2 ^ w) :
    (DataImplementation.select .unit payload hw fits).BoundedBy 5 23 :=
  ⟨fun _ => le_rfl, le_rfl⟩

theorem Natural.constant_boundedBy (input : Layout w A) (bound value : Nat) (hw : 16 < 2 ^ w)
    (fits : bound ≤ 2 ^ w) (valid : value < bound) :
    (Natural.constant .unit (by decide) input bound value hw fits valid).BoundedBy 7 35 :=
  ⟨fun _ => le_rfl, le_rfl⟩

theorem ListData.empty_boundedBy (input : Layout w B) (entry : Layout w A) (capacity : Nat)
    (hw : 16 < 2 ^ w) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.representation.encoding.words < 2 ^ w) :
    (ListData.empty .unit (by decide) input entry capacity hw countFits storageFits).BoundedBy
      (8 * (1 + capacity * entry.representation.encoding.words))
      (26 * (1 + capacity * entry.representation.encoding.words) + 14) := by
  constructor
  · intro value
    exact (Assembly.code_time_unit_le (List.replicate (1 + capacity * entry.representation.encoding.words)
      (.literal 0 : Assembly.Operand w))).trans (by simp)
  · exact (Assembly.code_descriptionWords_le (List.replicate (1 + capacity * entry.representation.encoding.words)
      (.literal 0 : Assembly.Operand w))).trans (by simp)

theorem ListData.widen_boundedBy (entry : Layout w A) (source target : Nat) (increasing : source ≤ target)
    (hw : 16 < 2 ^ w) (countFits : target < 2 ^ w)
    (storageFits : 1 + target * entry.representation.encoding.words < 2 ^ w) :
    (ListData.widen .unit (by decide) entry source target increasing hw countFits storageFits).BoundedBy
      (8 * (1 + target * entry.representation.encoding.words))
      (26 * (1 + target * entry.representation.encoding.words) + 14) :=
  ⟨fun _ => ListCapacity.time_unit_le _ _ _ increasing, ListCapacity.descriptionWords_le _ _ _ increasing⟩

end Signatures.Runtime.CaliperBackend.BoundedSource
