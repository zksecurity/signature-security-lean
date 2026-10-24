import Proofs.Runtime.Caliper.Boolean
import Proofs.Runtime.Caliper.SourceLists

/-! Unit and Boolean source operations on bounded layouts. Conditional selection
changes the stored Boolean into a union tag by executed instructions; the payload
keeps its original validity predicate and stored words. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.DataImplementation

open Caliper

variable {w : Nat} {A : Type}

def unitLayout (w : Nat) : Layout w Unit :=
  Layout.all ⟨Encoding.unit w, by change 0 < 2 ^ w; positivity⟩

def boolLayout (w : Nat) (hw : 0 < w) : Layout w Bool :=
  Layout.all (Representation.boolean w hw)

def unit (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord) (input : Layout w A)
    (hw : 16 < 2 ^ w) : Implementation cost input (unitLayout w) (fun _ => ()) where
  preserves _ _ := trivial
  program := Assembly.realizer cost allocation input.representation _ _ [] hw rfl
    (by simp) (by simp [Assembly.Valid]) (fun _ _ _ => rfl)

def boolean (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord) (input : Layout w A)
    (value : Bool) (hw : 16 < 2 ^ w) :
    Implementation cost input (boolLayout w (width_pos hw)) (fun _ => value) where
  preserves _ _ := trivial
  program := (Boolean.constant cost allocation input.representation value hw).viewOutput _ _ (fun _ => rfl)

def select (cost : CostModel) (payload : Layout w A) (hw : 16 < 2 ^ w)
    (fits : 1 + payload.representation.encoding.words < 2 ^ w) :
    Implementation cost ((boolLayout w (width_pos hw)).prod payload fits)
      (payload.sum payload (width_pos hw) (by simpa using fits)) Boolean.select where
  preserves value valid := by
    change Sum.elim payload.valid payload.valid (Boolean.select value)
    cases condition : value.1 <;> simpa [Boolean.select, condition] using valid.2
  program := ((Boolean.selectRealizer cost payload.representation hw fits).viewInput _
    (fun value : ((boolLayout w (width_pos hw)).prod payload fits).Value =>
      (value.val.1, ⟨value.val.2, value.property.2⟩)) (fun _ => rfl)).viewOutput _ _ (by
        rintro ⟨⟨condition, value⟩, valid⟩
        cases condition <;> rfl)

end Signatures.Runtime.CaliperBackend.BoundedSource.DataImplementation
