import Proofs.Runtime.SeededDeferred
import Proofs.Runtime.SeededTrace

/-! Joint deferred sampling with the complete first-run transcript and the
original seed available to the continuation. This is the form needed before
resetting one family for a second execution. -/

open OracleComp OracleSpec MeasureTheory

namespace Signatures.Runtime.SeededDeferred

variable {I A B : Type} {spec : OracleSpec I} [DecidableEq I]

theorem logged_bound (main : OracleComp spec A) (budget : I → Nat)
    (bound : IsPerIndexQueryBound main budget) :
    IsPerIndexQueryBound main.withQueryLog budget := by
  apply (isPerIndexQueryBound_iff_of_map_eq
    (show Prod.fst <$> main.withQueryLog = main by
      rw [withQueryLog, QueryImpl.fst_map_run_withLogging, simulateQ_ofLift_eq_self])).mpr
  exact bound

variable [∀ i, SampleableType (spec.Range i)] [IsUniformSpec spec]
  [∀ i, MeasurableSpace (spec.Range i)] [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] [MeasurableSpace B]

/-- The continuation can inspect the entire original seed. After deferral it
receives that seed reconstructed from the actual first transcript and an
independently generated unused suffix, with their full correlation preserved. -/
theorem defer_original_seed (main : OracleComp spec A) (budget : I → Nat)
    (bound : IsPerIndexQueryBound main budget) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families)
    (next : (A × QueryLog spec) → QuerySeed spec → OracleComp spec B) :
    𝒟[do
      let seed ← liftComp (generateSeed spec budget families) spec
      let result ← (simulateQ seededOracle main.withQueryLog).run seed
      next result.1 seed] =
    𝒟[do
      let result ← (simulateQ budgetOracle main.withQueryLog).run budget
      let rest ← liftComp (generateSeed spec result.2 families) spec
      next result.1 (SeededTrace.restore result.1.2 rest)] := by
  trans 𝒟[do
    let seed ← liftComp (generateSeed spec budget families) spec
    let result ← (simulateQ seededOracle main.withQueryLog).run seed
    next result.1 (SeededTrace.restore result.1.2 result.2)]
  · apply measure_of_compat
    apply congrArg SPMF.toMeasure
    apply evalSPMF_bind_congr
    intro seed hseed
    apply evalSPMF_bind_congr
    intro result hresult
    have capacity : ∀ i, budget i ≤ (seed i).length :=
      generateSeed_covers_queryBound budget families cover (by simpa only [support_liftComp] using hseed)
    rw [SeededTrace.restore_run main budget bound seed capacity result hresult]
  · exact defer main.withQueryLog budget (logged_bound main budget bound)
      families unique cover (fun result rest => next result (SeededTrace.restore result.2 rest))

end Signatures.Runtime.SeededDeferred
