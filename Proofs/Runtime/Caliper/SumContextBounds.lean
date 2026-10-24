import Proofs.Runtime.Caliper.SumContext

/-! Resource bounds for moving union padding across a saved context. Both stored
branches are counted, while execution time counts only the selected branch. -/

namespace Signatures.Runtime.CaliperBackend.SumContext
open Caliper Assembly

variable {w : Nat} {A B S : Type}

theorem unpad_time (value : Representation w A) (saved : Representation w S) (padding : Nat)
    (hw : 16 < 2 ^ w) (fits : value.encoding.words + padding + saved.encoding.words < 2 ^ w)
    (x : A × S) : (unpad value saved padding hw fits).time x ≤
      8 * (value.encoding.words + saved.encoding.words) := by
  have bound := code_time_unit_le
    (reads (w := w) 0 0 value.encoding.words ++ reads 0 (value.encoding.words + padding) saved.encoding.words)
  simp only [List.length_append, reads_length] at bound
  exact bound

theorem unpad_words (value : Representation w A) (saved : Representation w S) (padding : Nat)
    (hw : 16 < 2 ^ w) (fits : value.encoding.words + padding + saved.encoding.words < 2 ^ w) :
    descriptionWords (unpad value saved padding hw fits).code ≤
      26 * (value.encoding.words + saved.encoding.words) + 14 := by
  have bound := code_descriptionWords_le
    (reads (w := w) 0 0 value.encoding.words ++ reads 0 (value.encoding.words + padding) saved.encoding.words)
  simp only [List.length_append, reads_length] at bound
  exact bound

theorem unpad_names (value : Representation w A) (saved : Representation w S) (padding : Nat)
    (hw : 16 < 2 ^ w) (fits : value.encoding.words + padding + saved.encoding.words < 2 ^ w) :
    NamesAccounted (unpad value saved padding hw fits).code 3 := by
  apply code_namesAccounted
  exact (sourcesBound_append _ _ _).mpr
    ⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩

variable (left : Representation w A) (right : Representation w B) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (fits : 1 + max left.encoding.words right.encoding.words + saved.encoding.words < 2 ^ w)

theorem time (x : (A ⊕ B) × S) : (distribute left right saved hw fits).time x ≤
    24 * (1 + max left.encoding.words right.encoding.words + saved.encoding.words) + 2 := by
  have frame := frame_words left right saved fits
  rcases x with ⟨a | b, s⟩
  · have unpadded := unpad_time left saved (max left.encoding.words right.encoding.words - left.encoding.words) hw (by omega) (a, s)
    have tagged := inl_time (left.prod saved (by omega)) (right.prod saved (by omega)) hw
      (output left right saved hw fits).fits (a, s)
    change 1 + (1 + ((selectSlice (w := w) 1 (leftFrame left right saved fits).encoding.words).staticTime .unit +
      ((unpad left saved _ hw _).time (a, s) + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    dsimp only [id]
    change _ ≤ 8 * (1 + max (left.encoding.words + saved.encoding.words)
      (right.encoding.words + saved.encoding.words)) at tagged
    dsimp only [CostModel.unit] at tagged
    omega
  · have unpadded := unpad_time right saved (max left.encoding.words right.encoding.words - right.encoding.words) hw (by omega) (b, s)
    have tagged := inr_time (left.prod saved (by omega)) (right.prod saved (by omega)) hw
      (output left right saved hw fits).fits (b, s)
    change 1 + (1 + ((selectSlice (w := w) 1 (rightFrame left right saved fits).encoding.words).staticTime .unit +
      ((unpad right saved _ hw _).time (b, s) + _))) ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    dsimp only [id]
    change _ ≤ 8 * (1 + max (left.encoding.words + saved.encoding.words)
      (right.encoding.words + saved.encoding.words)) at tagged
    dsimp only [CostModel.unit] at tagged
    omega

theorem words : descriptionWords (distribute left right saved hw fits).code ≤
    156 * (1 + max left.encoding.words right.encoding.words + saved.encoding.words) + 95 := by
  have one := unpad_words left saved (max left.encoding.words right.encoding.words - left.encoding.words) hw (by omega)
  have two := unpad_words right saved (max left.encoding.words right.encoding.words - right.encoding.words) hw (by omega)
  have taggedLeft := inl_words (left.prod saved (by omega)) (right.prod saved (by omega)) hw
    (output left right saved hw fits).fits
  have taggedRight := inr_words (left.prod saved (by omega)) (right.prod saved (by omega)) hw
    (output left right saved hw fits).fits
  have frame := frame_words left right saved fits
  change descriptionWords (Dispatch.code (_ ;; _) (_ ;; _)
    (leftFrame left right saved fits).encoding.words (rightFrame left right saved fits).encoding.words) ≤ _
  rw [Dispatch.code_descriptionWords, descriptionWords_seq, descriptionWords_seq]
  change _ ≤ 26 * (1 + max (left.encoding.words + saved.encoding.words)
    (right.encoding.words + saved.encoding.words)) + 14 at taggedLeft taggedRight
  omega

theorem names : NamesAccounted (distribute left right saved hw fits).code 3 := by
  exact Dispatch.names
    ((unpad_names left saved _ hw _).seq (inl_names _ _ hw _).accounted)
    ((unpad_names right saved _ hw _).seq (inr_names _ _ hw _).accounted) _ _

end Signatures.Runtime.CaliperBackend.SumContext
