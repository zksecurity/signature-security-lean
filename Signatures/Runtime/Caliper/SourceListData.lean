import Signatures.Runtime.Caliper.SourceLists
import Signatures.Runtime.Caliper.ListLayout

/-! Source list constructors with validity predicates on the entries. The
underlying code is the executed bounded-list implementation, with subtype
witnesses erased through proved equalities of the stored lists. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.ListData

open Caliper

variable {w : Nat} {A B : Type}

def empty (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (input : Layout w B) (entry : Layout w A) (capacity : Nat)
    (hw : 16 < 2 ^ w) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.representation.encoding.words < 2 ^ w) :
    Implementation cost input (entry.boundedList capacity countFits storageFits) (fun _ => []) where
  preserves _ _ := by simp [Layout.boundedList]
  program := (ListConstruct.emptyRealizer cost allocation input.representation entry.representation capacity hw
    countFits storageFits).viewOutput _ _ (fun _ => rfl)

def consInput (entry : Layout w A) (capacity : Nat) (_hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.representation.encoding.words < 2 ^ w) : Layout w (A × List A) :=
  entry.prod (entry.boundedList capacity (by omega) (by nlinarith)) (by
    change entry.representation.encoding.words + (1 + capacity * entry.representation.encoding.words) < 2 ^ w
    nlinarith)

def cons (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.representation.encoding.words < 2 ^ w) :
    Implementation cost (consInput entry capacity hw countFits storageFits)
      (entry.boundedList (capacity + 1) countFits storageFits) (fun value => value.1 :: value.2) where
  preserves value valid := by
    change (value.1 :: value.2).length ≤ capacity + 1 ∧ ∀ x ∈ value.1 :: value.2, entry.valid x
    exact ⟨by simpa using Nat.add_le_add_right valid.2.1 1,
      by intro x member; rcases List.mem_cons.mp member with rfl | member
         · exact valid.1
         · exact valid.2.2 x member⟩
  program := ((ListConstruct.realizer cost allocation entry.representation capacity hw countFits storageFits).viewInput _
    (fun value : (consInput entry capacity hw countFits storageFits).Value =>
      (⟨value.val.1, value.property.1⟩, listView entry capacity ⟨value.val.2, value.property.2⟩)) (fun _ => rfl)).viewOutput _ _ (by
        intro value
        apply congrArg (entry.representation.boundedList (capacity + 1) countFits storageFits).encoding.encode
        apply Subtype.ext
        apply List.map_injective_iff.mpr Subtype.val_injective
        exact (listView_values entry (capacity + 1) _).trans
          (congrArg (List.cons value.val.1) (listView_values entry capacity ⟨value.val.2, value.property.2⟩).symm))

def widen (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Layout w A) (source target : Nat) (increasing : source ≤ target)
    (hw : 16 < 2 ^ w) (countFits : target < 2 ^ w)
    (storageFits : 1 + target * entry.representation.encoding.words < 2 ^ w) :
    Implementation cost
      (entry.boundedList source (increasing.trans_lt countFits) (by nlinarith))
      (entry.boundedList target countFits storageFits) id where
  preserves _ valid := ⟨valid.1.trans increasing, valid.2⟩
  program := ((ListCapacity.realizer cost allocation entry.representation source target increasing hw countFits storageFits).viewInput _
    (listView entry source) (fun _ => rfl)).viewOutput _ _ (by
      intro value
      apply congrArg (entry.representation.boundedList target countFits storageFits).encoding.encode
      apply Subtype.ext
      apply List.map_injective_iff.mpr Subtype.val_injective
      exact (listView_values entry target _).trans (listView_values entry source value).symm)

end Signatures.Runtime.CaliperBackend.BoundedSource.ListData
