import Proofs.Schnorr.FixedTapeExtraction
import Proofs.Schnorr.LazyROMReduction
import Proofs.Runtime.SeededForkReachability

/-! Schnorr's full lazy fork agrees with the fixed-private-tape reference.
The family cover is used only in the proof, and is deduplicated there. -/

open OracleComp OracleSpec
open Signatures.Runtime.SeededLazyFork

namespace Schnorr.LazyROM

variable {F A : Type} [SampleableType F] [DecidableEq F]

private theorem recordedFork_castSucc (main : OracleComp (FixedTape.Spec F) A) (q : Nat)
    (select : A → Option (Fin q)) :
    recordedFork main (.inr ()) (Option.map Fin.castSucc ∘ select) =
      recordedFork main (.inr ()) select := by
  unfold recordedFork
  apply bind_congr
  intro first
  cases selected : select first.1 with
  | none => simp [afterFirst, selected]
  | some slot =>
      simp only [afterFirst, Function.comp_def, selected, Option.map_some]
      apply bind_congr
      intro answer
      simp only [Fin.val_castSucc]
      split
      · rfl
      · apply bind_congr
        intro second
        have hsame : Option.map Fin.castSucc (select second) = some slot.castSucc ↔
            select second = some slot := by
          simpa only [Option.map_some] using
            (Option.map_injective (Fin.castSucc_injective q)).eq_iff
              (a := select second) (b := some slot)
        simp only [hsame]

omit [SampleableType F] [DecidableEq F] in
theorem finiteBounds_dedup (privateFamilies : List Nat) (qR qH : Nat) :
    FixedTape.finiteBounds privateFamilies.dedup qR qH =
      FixedTape.finiteBounds privateFamilies qR qH := by
  funext i
  cases i <;> simp [FixedTape.finiteBounds]

omit [SampleableType F] [DecidableEq F] in
theorem seedFamilies_dedup_nodup (privateFamilies : List Nat) :
    (FixedTape.seedFamilies privateFamilies.dedup).Nodup := by
  simp only [FixedTape.seedFamilies, List.nodup_append]
  refine ⟨List.Nodup.map Sum.inl_injective (List.nodup_dedup _), by simp, ?_⟩
  simp

variable [Fintype F] [Inhabited F]
  [MeasurableSpace F] [DiscreteMeasurableSpace F] [MeasurableSpace A]

noncomputable local instance forkUniformChallenges : IsUniformSpec (Unit →ₒ F) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable local instance forkNativeMeasure : IsUniformMeasureSpec (FixedTape.Spec F) :=
  OracleSpec.instIsUniformMeasureSpecOfIsUniformSpec

/-- The complete joint law, with the same selectable `qH + 1` labels. The
proof-only list may contain duplicates; its membership-based bound is unchanged
by deduplication. All private draws, including post-fork draws, are retained. -/
theorem fork_eq_complete (main : OracleComp (FixedTape.Spec F) A)
    (privateFamilies : List Nat) (qR qH : Nat)
    (select : A → Option (Fin (qH + 1)))
    (bound : IsPerIndexQueryBound main (FixedTape.finiteBounds privateFamilies qR (qH + 1)))
    (reachable : PathCfReachable main (FiatShamir.nmaForkBudget qH) (.inr ()) select) :
    𝒟[fork main qH select] =
      𝒟[FixedTape.completeFork main privateFamilies.dedup qR qH select] := by
  have hbound : IsPerIndexQueryBound main
      (FixedTape.finiteBounds privateFamilies.dedup qR (qH + 1)) := by
    rw [finiteBounds_dedup]
    exact bound
  have hreach : PathCfReachable main
      (FixedTape.finiteBounds privateFamilies.dedup qR (qH + 1)) (.inr ())
      (Option.map Fin.castSucc ∘ select) := by
    unfold PathCfReachable
    dsimp only [FixedTape.finiteBounds]
    intro path slot selected
    dsimp only [Function.comp_def] at selected
    rw [Option.map_eq_some_iff] at selected
    obtain ⟨original, selected, rfl⟩ := selected
    exact reachable path original selected
  have h := seededFork_eq_recordedFork_of_reachable main
    (FixedTape.finiteBounds privateFamilies.dedup qR (qH + 1)) hbound
    (FixedTape.seedFamilies privateFamilies.dedup) (seedFamilies_dedup_nodup privateFamilies)
    (fun i hi => FixedTape.seedFamilies_cover privateFamilies.dedup qR (qH + 1) i (Nat.ne_of_gt hi))
    (.inr ()) (Option.map Fin.castSucc ∘ select) hreach
  have hcast := recordedFork_castSucc main (qH + 1) select
  have h' : 𝒟[FixedTape.completeFork main privateFamilies.dedup qR qH select] =
      𝒟[recordedFork main (.inr ()) (Option.map Fin.castSucc ∘ select)] := h
  rw [hcast] at h'
  exact h'.symm

end Schnorr.LazyROM
