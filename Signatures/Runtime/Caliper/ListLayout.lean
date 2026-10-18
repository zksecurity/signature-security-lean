import Signatures.Runtime.Caliper.BoundedSource

/-! Lists whose entries themselves have bounded layouts. This keeps the original
mathematical element and list types, while proving that each stored entry belongs
to its representation's domain. Witnesses are absent from the word encoding. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

variable {w : Nat} {A : Type}

def listView (entry : Layout w A) (capacity : Nat) :
    {values : List A // values.length ≤ capacity ∧ ∀ value ∈ values, entry.valid value} ≃
      BoundedList entry.Value capacity where
  toFun values := ⟨values.val.attachWith entry.valid values.property.2, by simpa using values.property.1⟩
  invFun values := ⟨values.val.map Subtype.val, by
    constructor
    · simpa using values.property
    · intro value member
      obtain ⟨stored, _, equal⟩ := List.mem_map.mp member
      subst value
      exact stored.property⟩
  left_inv values := by
    apply Subtype.ext
    exact List.attachWith_map_subtype_val values.property.2
  right_inv values := by
    apply Subtype.ext
    apply List.map_injective_iff.mpr Subtype.val_injective
    exact List.attachWith_map_subtype_val _

def Layout.boundedList (entry : Layout w A) (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.representation.encoding.words < 2 ^ w) : Layout w (List A) where
  valid values := values.length ≤ capacity ∧ ∀ value ∈ values, entry.valid value
  representation := (entry.representation.boundedList capacity countFits storageFits).transport (listView entry capacity)

theorem listView_values (entry : Layout w A) (capacity : Nat)
    (values : {values : List A // values.length ≤ capacity ∧ ∀ value ∈ values, entry.valid value}) :
    (listView entry capacity values).val.map Subtype.val = values.val :=
  List.attachWith_map_subtype_val values.property.2

end Signatures.Runtime.CaliperBackend.BoundedSource
