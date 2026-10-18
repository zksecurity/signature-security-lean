import Signatures.Runtime.Caliper.ListNarrow

/-! Prepending within an existing list capacity. The input invariant supplies
one free entry slot. Executed prefix copying removes that unused padding before
the existing constructor runs, so the output retains the original capacity. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.ListData

open Caliper

variable {w : Nat} {A : Type}

def fixedConsInput (entry : Layout w A) (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
    (frameFits : 1 + (capacity + 2) * entry.representation.encoding.words < 2 ^ w) : Layout w (A × List A) :=
  (entry.prod (entry.boundedList (capacity + 1) countFits (by nlinarith))
    (by change entry.representation.encoding.words + (1 + (capacity + 1) * entry.representation.encoding.words) < 2 ^ w; nlinarith)).restrict
      (fun value => value.2.length ≤ capacity)

def fixedConsPrepare (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w) (countFits : capacity + 1 < 2 ^ w)
    (frameFits : 1 + (capacity + 2) * entry.representation.encoding.words < 2 ^ w) :
    Implementation cost (fixedConsInput entry capacity countFits frameFits)
      (consInput entry capacity hw countFits (by nlinarith)) id where
  preserves _ valid := ⟨valid.1.1, valid.2, valid.1.2.2⟩
  program := selectSliceRealizer cost allocation _ _ _ 0 hw
    (by change 0 + (entry.representation.encoding.words + (1 + capacity * entry.representation.encoding.words)) ≤
          entry.representation.encoding.words + (1 + (capacity + 1) * entry.representation.encoding.words); nlinarith)
    (by
      intro value
      let values := listView entry (capacity + 1) ⟨value.val.2, value.property.1.2⟩
      have length : values.val.length ≤ capacity := by simpa [values, listView] using value.property.2
      have prefixEq := Encoding.boundedList_take entry.representation.encoding (capacity + 1) capacity (by omega) countFits values length
      simp only [List.drop_zero]
      change (entry.representation.encoding.encode ⟨value.val.1, value.property.1.1⟩ ++
        (entry.representation.encoding.boundedList (capacity + 1) countFits).encode values).take
          (entry.representation.encoding.words + (1 + capacity * entry.representation.encoding.words)) =
        entry.representation.encoding.encode ⟨value.val.1, value.property.1.1⟩ ++
          (entry.representation.encoding.boundedList capacity (by omega)).encode ⟨values.val, length⟩
      rw [List.take_append, entry.representation.encoding.encode_length, Nat.add_sub_cancel_left,
        List.take_of_length_le (by rw [entry.representation.encoding.encode_length]; omega), prefixEq])

def fixedCons (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w) (countFits : capacity + 1 < 2 ^ w)
    (frameFits : 1 + (capacity + 2) * entry.representation.encoding.words < 2 ^ w) :
    Implementation cost (fixedConsInput entry capacity countFits frameFits)
      (entry.boundedList (capacity + 1) countFits (by nlinarith)) (fun value => value.1 :: value.2) :=
  (fixedConsPrepare cost allocation entry capacity hw countFits frameFits).then
    (cons cost allocation entry capacity hw countFits (by nlinarith))

theorem fixedConsPrepare_boundedBy (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w) (frameFits : 1 + (capacity + 2) * entry.representation.encoding.words < 2 ^ w) :
    (fixedConsPrepare .unit (by decide) entry capacity hw countFits frameFits).BoundedBy
      (8 * (1 + (capacity + 1) * entry.representation.encoding.words))
      (26 * (1 + (capacity + 1) * entry.representation.encoding.words) + 14) := by
  have width : (consInput entry capacity hw countFits (by nlinarith)).representation.encoding.words =
      1 + (capacity + 1) * entry.representation.encoding.words := by
    change entry.representation.encoding.words + (1 + capacity * entry.representation.encoding.words) = _
    ring
  constructor
  · intro value
    change (selectSlice (w := w) 0 _).staticTime .unit ≤ _
    rw [width]
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    omega
  · change descriptionWords (selectSlice (w := w) 0 _) ≤ _
    rw [width, selectSlice_descriptionWords]

theorem fixedCons_boundedBy (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w) (frameFits : 1 + (capacity + 2) * entry.representation.encoding.words < 2 ^ w) :
    (fixedCons .unit (by decide) entry capacity hw countFits frameFits).BoundedBy
      (16 * (1 + (capacity + 1) * entry.representation.encoding.words) + 5)
      (52 * (1 + (capacity + 1) * entry.representation.encoding.words) + 53) :=
  ((fixedConsPrepare_boundedBy entry capacity hw countFits frameFits).then
    (cons_boundedBy entry capacity hw countFits (by nlinarith))).mono (by omega) (by omega)

theorem fixedCons_buffers (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w) (frameFits : 1 + (capacity + 2) * entry.representation.encoding.words < 2 ^ w) :
    (fixedCons cost allocation entry capacity hw countFits frameFits).program.code.memBound ≤ 2 := by
  have copied := selectSlice_buffers (w := w) 0 (entry.representation.encoding.words + (1 + capacity * entry.representation.encoding.words))
  have constructed := (Assembly.code_names (ListConstruct.consOperands (w := w) entry.representation.encoding.words capacity) 1 (by
    simp only [ListConstruct.consOperands, Assembly.sourcesBound_append]
    exact ⟨⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩,
      Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).2
  have incremented := CellArithmetic.buffers (w := w) 0 .add 1
  change max _ (max _ _) ≤ 2
  exact max_le copied (max_le constructed (incremented.trans (by decide)))

theorem fixedCons_names (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w)
    (frameFits : 1 + (capacity + 2) * entry.representation.encoding.words < 2 ^ w) (slots : Nat) :
    NamesAccounted (fixedCons .unit (by decide) entry capacity hw countFits frameFits).program.code slots :=
  (selectSlice_names _ _ _).seq (cons_names entry capacity hw countFits (by nlinarith) slots)

end Signatures.Runtime.CaliperBackend.BoundedSource.ListData
