import Signatures.Runtime.Caliper.ListCases
import Signatures.Runtime.Caliper.ListCapacity
import Signatures.Runtime.Caliper.BoundedSource

/-! Bounded-domain implementations of the original mathematical list operations.
The source types remain `List A` and ordinary products/sums. Capacity witnesses
restrict the represented domain and are erased from the stored data. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {A B D : Type}

/-- A different mathematical input view is permitted only when its stored bytes
are proved identical. This executes the original body with its original costs. -/
def Realizer.viewInput {cost : CostModel} {input : Representation w A}
    {output : Representation w B} {f : A → B} (body : Realizer cost input output f)
    (source : Representation w D) (view : D → A)
    (sameBytes : ∀ value, source.encoding.encode value = input.encoding.encode (view value)) :
    Realizer cost source output (f ∘ view) where
  code := body.code
  positive_width := body.positive_width
  description_fits := body.description_fits
  random_free := body.random_free
  time value := body.time (view value)
  net value := body.net (view value)
  workspace value := body.workspace (view value)
  correct tape value before represented :=
    body.correct tape (view value) before
      ⟨represented.1, represented.2.1.trans (sameBytes value), represented.2.2⟩

namespace BoundedSource.ListImplementation

def empty (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (input : Layout w B) (entry : Representation w A) (capacity : Nat)
    (hw : 16 < 2 ^ w) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words < 2 ^ w) :
    Implementation cost input (Layout.list entry capacity countFits storageFits) (fun _ => []) where
  preserves _ _ := by simp [Layout.list]
  program := ListConstruct.emptyRealizer cost allocation input.representation entry capacity hw countFits storageFits

def cons (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.encoding.words < 2 ^ w) :
    Implementation cost
      ((Layout.all entry).prod (Layout.list entry capacity (by omega) (by nlinarith)) (by
        change entry.encoding.words + (1 + capacity * entry.encoding.words) < 2 ^ w
        nlinarith))
      (Layout.list entry (capacity + 1) countFits storageFits) (fun value => value.1 :: value.2) where
  preserves value valid := by
    change (value.1 :: value.2).length ≤ capacity + 1
    exact Nat.add_le_add_right valid.2 1
  program := (ListConstruct.realizer cost allocation entry capacity hw countFits storageFits).viewInput _
    (fun value : {value : A × List A // True ∧ value.2.length ≤ capacity} =>
      (value.val.1, ⟨value.val.2, value.property.2⟩)) (fun _ => rfl)

def widen (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (source target : Nat) (increasing : source ≤ target)
    (hw : 16 < 2 ^ w) (countFits : target < 2 ^ w)
    (storageFits : 1 + target * entry.encoding.words < 2 ^ w) :
    Implementation cost (Layout.list entry source (increasing.trans_lt countFits) (by nlinarith))
      (Layout.list entry target countFits storageFits) id where
  preserves _ valid := valid.trans increasing
  program := ListCapacity.realizer cost allocation entry source target increasing hw countFits storageFits

def caseList : List A → Unit ⊕ (A × List A)
  | [] => .inl ()
  | head :: tail => .inr (head, tail)

def caseValid (capacity : Nat) : Unit ⊕ (A × List A) → Prop
  | .inl _ => True
  | .inr value => value.2.length ≤ capacity

def caseView (capacity : Nat) :
    {value : Unit ⊕ (A × List A) // caseValid capacity value} ≃ (Unit ⊕ (A × BoundedList A capacity)) where
  toFun value := match value with
    | ⟨.inl token, _⟩ => .inl token
    | ⟨.inr (head, tail), valid⟩ => .inr (head, ⟨tail, valid⟩)
  invFun value := match value with
    | .inl token => ⟨.inl token, trivial⟩
    | .inr (head, tail) => ⟨.inr (head, tail.val), tail.property⟩
  left_inv value := by rcases value with ⟨value, valid⟩; cases value <;> rfl
  right_inv value := by cases value <;> rfl

def caseOutput (entry : Representation w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w) (storageFits : ListDestruct.outputWords entry.encoding.words capacity < 2 ^ w) :
    Layout w (Unit ⊕ (A × List A)) where
  valid := caseValid capacity
  representation := (ListDestruct.output entry capacity hw countFits storageFits).transport (caseView capacity)

def cases (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w) (storageFits : ListDestruct.outputWords entry.encoding.words capacity < 2 ^ w) :
    Implementation cost (Layout.list entry (capacity + 1) countFits (by dsimp [ListDestruct.outputWords] at storageFits; omega))
      (caseOutput entry capacity hw countFits storageFits) caseList where
  preserves value valid := by
    cases value with
    | nil => trivial
    | cons head tail => simpa [caseOutput, caseValid, caseList, Layout.list] using valid
  program := (ListDestruct.realizer cost allocation entry capacity hw countFits storageFits).viewOutput _ _ (by
    rintro ⟨value, valid⟩
    cases value <;> rfl)

end BoundedSource.ListImplementation
end Signatures.Runtime.CaliperBackend
