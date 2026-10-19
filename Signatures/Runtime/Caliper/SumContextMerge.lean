import Signatures.Runtime.Caliper.SumContextBounds

/-! The executed inverse of union/context distribution. In particular, the
saved context moves past union padding; the mathematical equivalence alone
does not implement this change in memory. Both stored branches are charged. -/

namespace Signatures.Runtime.CaliperBackend.SumContext
open Caliper

variable {w : Nat} {A B S : Type}
    (left : Representation w A) (right : Representation w B) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (fits : 1 + max left.encoding.words right.encoding.words + saved.encoding.words < 2 ^ w)

def mergeLeft : Realizer .unit (left.prod saved (by omega)) (input left right saved hw fits)
    (fun value => (Sum.inl value.1, value.2)) :=
  (inlRealizer .unit (by decide) left right hw (by omega)).retain (by decide) saved hw
    (by
      have := (inl_names left right hw (by omega)).buffers
      dsimp only [Realizer.savedBuffer]
      omega)
    (by omega) fits

def mergeRight : Realizer .unit (right.prod saved (by omega)) (input left right saved hw fits)
    (fun value => (Sum.inr value.1, value.2)) :=
  (inrRealizer .unit (by decide) left right hw (by omega)).retain (by decide) saved hw
    (by
      have := (inr_names left right hw (by omega)).buffers
      dsimp only [Realizer.savedBuffer]
      omega)
    (by omega) fits

def merge : Realizer .unit (output left right saved hw fits) (input left right saved hw fits) view.symm :=
  (branchRealizer .unit (by decide) (left.prod saved (by omega)) (right.prod saved (by omega)) _
    (mergeLeft left right saved hw fits) (mergeRight left right saved hw fits)
    hw (output left right saved hw fits).fits).viewOutput (input left right saved hw fits) view.symm (by
      intro value
      rcases value with ⟨a, s⟩ | ⟨b, s⟩ <;> rfl)

theorem mergeLeft_time (value : A × S) : (mergeLeft left right saved hw fits).time value ≤
    36 * (1 + max left.encoding.words right.encoding.words + saved.encoding.words) := by
  have tagged := inl_time left right hw (by omega) value.1
  have copied := (inlRealizer .unit (by decide) left right hw (by omega)).retain_time_unit_le
    saved hw (by
      have := (inl_names left right hw (by omega)).buffers
      dsimp only [Realizer.savedBuffer]
      omega) (by omega) fits value
  change _ ≤ _ + 8 * left.encoding.words + 8 * (1 + max left.encoding.words right.encoding.words) +
    12 * saved.encoding.words at copied
  exact copied.trans (by omega)

theorem mergeRight_time (value : B × S) : (mergeRight left right saved hw fits).time value ≤
    36 * (1 + max left.encoding.words right.encoding.words + saved.encoding.words) := by
  have tagged := inr_time left right hw (by omega) value.1
  have copied := (inrRealizer .unit (by decide) left right hw (by omega)).retain_time_unit_le
    saved hw (by
      have := (inr_names left right hw (by omega)).buffers
      dsimp only [Realizer.savedBuffer]
      omega) (by omega) fits value
  change _ ≤ _ + 8 * right.encoding.words + 8 * (1 + max left.encoding.words right.encoding.words) +
    12 * saved.encoding.words at copied
  exact copied.trans (by omega)

theorem mergeLeft_words : descriptionWords (mergeLeft left right saved hw fits).code ≤
    117 * (1 + max left.encoding.words right.encoding.words + saved.encoding.words) + 53 := by
  have tagged := inl_words left right hw (by omega)
  have copied := (inlRealizer .unit (by decide) left right hw (by omega)).retain_descriptionWords_le
    (by decide) saved hw (by
      have := (inl_names left right hw (by omega)).buffers
      dsimp only [Realizer.savedBuffer]
      omega) (by omega) fits
  change _ ≤ _ + 26 * left.encoding.words + 26 * (1 + max left.encoding.words right.encoding.words) +
    39 * saved.encoding.words + 39 at copied
  exact copied.trans (by omega)

theorem mergeRight_words : descriptionWords (mergeRight left right saved hw fits).code ≤
    117 * (1 + max left.encoding.words right.encoding.words + saved.encoding.words) + 53 := by
  have tagged := inr_words left right hw (by omega)
  have copied := (inrRealizer .unit (by decide) left right hw (by omega)).retain_descriptionWords_le
    (by decide) saved hw (by
      have := (inr_names left right hw (by omega)).buffers
      dsimp only [Realizer.savedBuffer]
      omega) (by omega) fits
  change _ ≤ _ + 26 * right.encoding.words + 26 * (1 + max left.encoding.words right.encoding.words) +
    39 * saved.encoding.words + 39 at copied
  exact copied.trans (by omega)

theorem merge_time (value : (A × S) ⊕ (B × S)) : (merge left right saved hw fits).time value ≤
    44 * (1 + max left.encoding.words right.encoding.words + saved.encoding.words) + 2 := by
  rcases value with value | value
  · have bound := mergeLeft_time left right saved hw fits value
    change 1 + (1 + ((selectSlice (w := w) 1 (left.encoding.words + saved.encoding.words)).staticTime .unit + _)) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    dsimp only [CostModel.unit] at bound
    omega
  · have bound := mergeRight_time left right saved hw fits value
    change 1 + (1 + ((selectSlice (w := w) 1 (right.encoding.words + saved.encoding.words)).staticTime .unit + _)) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    dsimp only [CostModel.unit] at bound
    omega

theorem merge_words : descriptionWords (merge left right saved hw fits).code ≤
    286 * (1 + max left.encoding.words right.encoding.words + saved.encoding.words) + 143 := by
  have one := mergeLeft_words left right saved hw fits
  have two := mergeRight_words left right saved hw fits
  change descriptionWords (Dispatch.code _ _ (left.encoding.words + saved.encoding.words)
    (right.encoding.words + saved.encoding.words)) ≤ _
  rw [Dispatch.code_descriptionWords]
  omega

theorem merge_names : NamesAccounted (merge left right saved hw fits).code 3 :=
  Dispatch.names
    (Retain.names (inl_names left right hw (by omega)).accounted _ _ _)
    (Retain.names (inr_names left right hw (by omega)).accounted _ _ _) _ _

end Signatures.Runtime.CaliperBackend.SumContext
