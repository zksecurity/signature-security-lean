import Signatures.Runtime.Caliper.RestrictedLayout
import Signatures.Runtime.Caliper.BufferBounds

/-! Shrinking list storage when a proved length bound makes the discarded
suffix padding. The prefix is copied by actual memory instructions. No entry
is dropped and no encoding change is treated as a free view. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat} {A : Type}

theorem Encoding.boundedList_take (encoding : Encoding w A) (source target : Nat)
    (decreasing : target ≤ source) (sourceFits : source < 2 ^ w)
    (value : BoundedList A source) (length : value.val.length ≤ target) :
    ((encoding.boundedList source sourceFits).encode value).take (1 + target * encoding.words) =
      (encoding.boundedList target (decreasing.trans_lt sourceFits)).encode ⟨value.val, length⟩ := by
  change (BitVec.ofNat w value.val.length ::
    (encoding.pack value.val ++ List.replicate ((source - value.val.length) * encoding.words) 0)).take
      (1 + target * encoding.words) =
    BitVec.ofNat w value.val.length ::
      (encoding.pack value.val ++ List.replicate ((target - value.val.length) * encoding.words) 0)
  have packed : (encoding.pack value.val).length ≤ target * encoding.words := by
    rw [encoding.pack_length]
    exact Nat.mul_le_mul_right _ length
  have padding : (target - value.val.length) * encoding.words ≤ (source - value.val.length) * encoding.words := by
    exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right decreasing _)
  rw [Nat.add_comm 1, List.take_succ_cons, List.take_append, List.take_of_length_le packed,
    encoding.pack_length, ← Nat.sub_mul, List.take_replicate, Nat.min_eq_left padding]

namespace BoundedSource.ListData

def narrow (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Layout w A) (source target : Nat) (decreasing : target ≤ source)
    (hw : 16 < 2 ^ w) (countFits : source < 2 ^ w)
    (storageFits : 1 + source * entry.representation.encoding.words < 2 ^ w) :
    Implementation cost
      ((entry.boundedList source countFits storageFits).restrict (fun values => values.length ≤ target))
      (entry.boundedList target (decreasing.trans_lt countFits) (by nlinarith)) id where
  preserves _ valid := ⟨valid.2, valid.1.2⟩
  program := selectSliceRealizer cost allocation _ _ _ 0 hw
    (by change 0 + (1 + target * entry.representation.encoding.words) ≤ 1 + source * entry.representation.encoding.words; nlinarith)
    (by
      intro value
      simp only [List.drop_zero]
      exact Encoding.boundedList_take entry.representation.encoding source target decreasing countFits
        (listView entry source ⟨value.val, value.property.1⟩) (by simpa [listView] using value.property.2))

theorem narrow_boundedBy (entry : Layout w A) (source target : Nat) (decreasing : target ≤ source)
    (hw : 16 < 2 ^ w) (countFits : source < 2 ^ w)
    (storageFits : 1 + source * entry.representation.encoding.words < 2 ^ w) :
    (narrow .unit (by decide) entry source target decreasing hw countFits storageFits).BoundedBy
      (8 * (1 + target * entry.representation.encoding.words))
      (26 * (1 + target * entry.representation.encoding.words) + 14) := by
  constructor
  · intro value
    change (selectSlice (w := w) 0 (1 + target * entry.representation.encoding.words)).staticTime .unit ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    omega
  · exact (selectSlice_descriptionWords _ _).le

theorem narrow_buffers (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Layout w A) (source target : Nat) (decreasing : target ≤ source)
    (hw : 16 < 2 ^ w) (countFits : source < 2 ^ w)
    (storageFits : 1 + source * entry.representation.encoding.words < 2 ^ w) :
    (narrow cost allocation entry source target decreasing hw countFits storageFits).program.code.memBound ≤ 2 :=
  selectSlice_buffers _ _

end BoundedSource.ListData
end Signatures.Runtime.CaliperBackend
