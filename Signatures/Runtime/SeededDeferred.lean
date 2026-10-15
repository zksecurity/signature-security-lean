import Signatures.Runtime.SeededDeferredStep

/-! Deferred generation of unused seed entries after an adaptive computation.
The budget state is proof instrumentation, not an executable sampling-family
table. The theorem retains the complete residual seed in its continuation. -/

open OracleComp OracleSpec
open MeasureTheory

namespace Signatures.Runtime.SeededDeferred

variable {I A B : Type} {spec : OracleSpec I} [DecidableEq I]

def budgetOracle : QueryImpl spec (StateT (I → Nat) (OracleComp spec)) :=
  fun i budget => (fun answer => (answer, debit budget i)) <$>
    (liftM (spec.query i) : OracleComp spec _)

/-- Erasing the proof-only capacity counter gives the original live run. -/
theorem budget_run'_eq (main : OracleComp spec A) (budget : I → Nat) :
    (simulateQ budgetOracle main).run' budget = main := by
  induction main using OracleComp.inductionOn generalizing budget with
  | pure a => simp
  | query_bind i next ih =>
      simp only [StateT.run'_eq, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change Prod.fst <$> ((fun answer => (answer, debit budget i)) <$>
        (liftM (spec.query i) : OracleComp spec _) >>=
          fun p => (simulateQ budgetOracle (next p.1)).run p.2) = _
      rw [bind_map_left, map_bind]
      simpa only [StateT.run'_eq] using congrArg
        (fun f => (liftM (spec.query i) : OracleComp spec _) >>= f)
        (funext fun answer => ih answer (debit budget i))

variable [∀ i, SampleableType (spec.Range i)] [IsUniformSpec spec]
  [∀ i, MeasurableSpace (spec.Range i)] [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec]
  [MeasurableSpace B]

/-- Running against a full seed, then passing its unused entries to a
continuation, has the same joint law as running live while counting consumed
entries, then independently generating exactly the unused entries. Applying
this to a logged computation retains its full first-run transcript as well. -/
theorem defer (main : OracleComp spec A) (budget : I → Nat)
    (bound : IsPerIndexQueryBound main budget) (families : List I)
    (unique : families.Nodup) (cover : SeedListCovers budget families)
    (next : A → QuerySeed spec → OracleComp spec B) :
    𝒟[do
      let seed ← liftComp (generateSeed spec budget families) spec
      let result ← (simulateQ seededOracle main).run seed
      next result.1 result.2] =
    𝒟[do
      let result ← (simulateQ budgetOracle main).run budget
      let rest ← liftComp (generateSeed spec result.2 families) spec
      next result.1 rest] := by
  induction main using OracleComp.inductionOn generalizing budget with
  | pure a => simp
  | query_bind i continuation ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at bound
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      rw [query_bind_step (spec := spec) budget families unique cover i bound.1
        (fun answer seed => do
          let result ← (simulateQ seededOracle (continuation answer)).run seed
          next result.1 result.2)]
      simp only [budgetOracle, StateT.run, bind_map_left]
      let : MeasurableSpace (spec.Range i) := ⊤
      rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
      apply Measure.bind_congr_right
      apply Filter.Eventually.of_forall
      intro answer
      exact ih answer (debit budget i) (bound.2 answer)
        (debit_covers budget families cover i)

end Signatures.Runtime.SeededDeferred
