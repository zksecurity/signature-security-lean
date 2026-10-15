import Signatures.Runtime.SeededDeferredTrace
import Signatures.Runtime.SeededSuffixSampling

/-! Eliminating unused seed generation after a logged first execution. The
continuation law is checked only on supported transcripts. Its intermediate
state and transcript types need no countability assumptions. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.SeededDeferred

variable {I A B : Type} {spec : OracleSpec I} [DecidableEq I]

theorem budget_result_supported (main : OracleComp spec A) (budget : I → Nat)
    (result : A × (I → Nat))
    (supported : result ∈ support ((simulateQ budgetOracle main).run budget)) :
    result.1 ∈ support main := by
  rw [← budget_run'_eq main budget, StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

theorem logged_run_erase (main : OracleComp spec A) (seed : QuerySeed spec) :
    (fun result => result.1.1) <$>
      (simulateQ seededOracle main.withQueryLog).run seed =
      (simulateQ seededOracle main).run' seed := by
  have erased : Prod.fst <$> main.withQueryLog = main := by
    rw [withQueryLog, QueryImpl.fst_map_run_withLogging, simulateQ_ofLift_eq_self]
  have h := congrArg (fun computation => (simulateQ seededOracle computation).run' seed) erased
  simpa only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Function.comp_def] using h

variable [∀ i, SampleableType (spec.Range i)] [IsUniformSpec spec]
  [∀ i, MeasurableSpace (spec.Range i)] [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] [MeasurableSpace B]

/-- Replace a continuation using the full original seed by its lazy version,
once independent unused suffixes have been eliminated on every supported log. -/
theorem defer_continuation (main : OracleComp spec A) (budget : I → Nat)
    (bound : IsPerIndexQueryBound main budget) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families)
    (next : (A × QueryLog spec) → QuerySeed spec → OracleComp spec B)
    (lazyNext : (A × QueryLog spec) → OracleComp spec B)
    (suffixLaw : ∀ result ∈ support main.withQueryLog, ∀ remaining : I → Nat,
      𝒟[do
        let rest ← liftComp (generateSeed spec remaining families) spec
        next result (SeededTrace.restore result.2 rest)] = 𝒟[lazyNext result]) :
    𝒟[do
      let seed ← liftComp (generateSeed spec budget families) spec
      let result ← (simulateQ seededOracle main.withQueryLog).run seed
      next result.1 seed] =
    𝒟[main.withQueryLog >>= lazyNext] := by
  rw [defer_original_seed main budget bound families unique cover next]
  trans 𝒟[do
    let result ← (simulateQ budgetOracle main.withQueryLog).run budget
    lazyNext result.1]
  · apply OracleComp.evalDist_bind_congr_of_support
    intro result supported
    exact suffixLaw result.1 (budget_result_supported main.withQueryLog budget result supported) result.2
  · congr 1
    conv_rhs => rw [← budget_run'_eq main.withQueryLog budget, StateT.run'_eq, bind_map_left]

/-- A second execution can use just the first transcript, reset at a selected
prefix slot. This equality keeps any first-run information included in `replay`
and permits a different adaptive second computation. -/
theorem defer_reset_run (main : OracleComp spec A) (budget : I → Nat)
    (bound : IsPerIndexQueryBound main budget) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families)
    (replay : (A × QueryLog spec) → OracleComp spec B) (target : I)
    (slot : (A × QueryLog spec) → Nat)
    (answer : (A × QueryLog spec) → spec.Range target)
    (within : ∀ result ∈ support main.withQueryLog,
      slot result ≤ (SeededTrace.restore result.2 ∅ target).length) :
    𝒟[do
      let seed ← liftComp (generateSeed spec budget families) spec
      let result ← (simulateQ seededOracle main.withQueryLog).run seed
      (simulateQ seededOracle (replay result.1)).run'
        ((seed.takeAtIndex target (slot result.1)).addValue target (answer result.1))] =
    𝒟[do
      let result ← main.withQueryLog
      (simulateQ seededOracle (replay result)).run'
        (((SeededTrace.restore result.2 ∅).takeAtIndex target (slot result)).addValue target (answer result))] := by
  refine defer_continuation main budget bound families unique cover
    (fun result seed => (simulateQ seededOracle (replay result)).run'
      ((seed.takeAtIndex target (slot result)).addValue target (answer result)))
    (fun result => (simulateQ seededOracle (replay result)).run'
      (((SeededTrace.restore result.2 ∅).takeAtIndex target (slot result)).addValue target (answer result))) ?_
  intro result supported remaining
  exact SeededTrace.generate_reset_run (replay result) remaining families result.2 target
    (slot result) (answer result) (within result supported)

end Signatures.Runtime.SeededDeferred
