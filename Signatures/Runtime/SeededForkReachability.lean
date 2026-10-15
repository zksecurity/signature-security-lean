import Signatures.Runtime.SeededLazyFork
import VCVio.CryptoFoundations.ReplayFork

/-! The existing intrinsic fork-selector reachability property guarantees the
strict transcript bound needed to preserve the old-answer collision check. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.SeededLazyFork

variable {I A : Type} {spec : OracleSpec I} [DecidableEq I]

theorem restore_length (log : QueryLog spec) (target : I) :
    (SeededTrace.restore log ∅ target).length = log.countQ (· = target) := by
  induction log with
  | nil => rfl
  | cons entry log ih =>
      rcases entry with ⟨i, answer⟩
      by_cases h : i = target
      · subst i
        simp [SeededTrace.restore, QueryLog.countQ_cons, ih]
      · simp [SeededTrace.restore, QueryLog.countQ_cons, h,
          QuerySeed.prependValues_of_ne _ _ (Ne.symm h), ih]

/-- Every supported logged execution comes from an intrinsic path. Therefore
the existing path-based selector invariant also applies to the retained tape. -/
theorem within_of_reachable (main : OracleComp spec A) (budget : I → Nat) (target : I)
    (select : A → Option (Fin (budget target + 1)))
    (reachable : PathCfReachable main budget target select)
    (result : A × QueryLog spec) (supported : result ∈ support main.withQueryLog)
    (slot : Fin (budget target + 1)) (selected : select result.1 = some slot) :
    slot.val < (SeededTrace.restore result.2 ∅ target).length := by
  change result ∈ support (replayFirstRun main) at supported
  rw [← map_replayPathResult_replayFirstPath] at supported
  change result ∈ support (replayPathResult main <$> replayFirstPath main) at supported
  rw [support_map] at supported
  obtain ⟨path, _, rfl⟩ := supported
  have h := reachable path slot selected
  rw [PFunctor.FreeM.Cursor.locateAt?_isSome_iff_lt_occurrences] at h
  rw [restore_length, QueryLog.countQ_eq_occurrences]
  exact h

variable [∀ i, SampleableType (spec.Range i)] [∀ i, DecidableEq (spec.Range i)]
  [IsUniformSpec spec]
  [∀ i, MeasurableSpace (spec.Range i)] [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] [MeasurableSpace A]

theorem seededFork_eq_recordedFork_of_reachable (main : OracleComp spec A) (budget : I → Nat)
    (bound : IsPerIndexQueryBound main budget) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families) (target : I)
    (select : A → Option (Fin (budget target + 1)))
    (reachable : PathCfReachable main budget target select) :
    𝒟[seededFork main budget families target select] =
      𝒟[recordedFork main target select] :=
  seededFork_eq_recordedFork main budget bound families unique cover target select
    (within_of_reachable main budget target select reachable)

end Signatures.Runtime.SeededLazyFork
