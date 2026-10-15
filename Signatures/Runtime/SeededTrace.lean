import Signatures.Runtime.Replay
import VCVio.OracleComp.QueryTracking.SeededOracle

/-! Reconstructing a covered seed from an adaptive execution's full query log
and unused entries. Coverage is essential: a live fallback answer was not part
of the original seed and cannot be reconstructed as if it had been. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.SeededTrace

variable {I A : Type} {spec : OracleSpec I} [DecidableEq I]

def restore : QueryLog spec → QuerySeed spec → QuerySeed spec
  | [], seed => seed
  | ⟨i, answer⟩ :: tail, seed => (restore tail seed).prependValues (i := i) [answer]

theorem run_logged_query_cons (i : I) (next : spec.Range i → OracleComp spec A)
    (seed : QuerySeed spec) (answer : spec.Range i) (tail : List (spec.Range i))
    (hit : seed i = answer :: tail) :
    (simulateQ seededOracle (OracleComp.queryBind i next).withQueryLog).run seed =
      (fun p => ((p.1.1, ⟨i, answer⟩ :: p.1.2), p.2)) <$>
        (simulateQ seededOracle (next answer).withQueryLog).run (seed.update i tail) := by
  rw [Replay.withQueryLog_queryBind]
  change (simulateQ seededOracle ((liftM (spec.query i) : OracleComp spec _) >>=
    fun a => (fun p => (p.1, ⟨i, a⟩ :: p.2)) <$> (next a).withQueryLog)).run seed = _
  simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_map, StateT.run_bind, StateT.run_map]
  rw [seededOracle.run_cons hit, pure_bind]

/-- When the seed covers every path, the consumed log plus the residual seed
recovers the entire initial seed, including private entries never requested. -/
theorem restore_run (main : OracleComp spec A) (budget : I → Nat)
    (bound : IsPerIndexQueryBound main budget) (seed : QuerySeed spec)
    (capacity : ∀ i, budget i ≤ (seed i).length)
    (p : (A × QueryLog spec) × QuerySeed spec)
    (hp : p ∈ support ((simulateQ seededOracle main.withQueryLog).run seed)) :
    restore p.1.2 p.2 = seed := by
  induction main using OracleComp.inductionOn generalizing budget seed p with
  | pure a =>
      have he : p = ((a, []), seed) := by simpa using hp
      subst p
      rfl
  | query_bind i next ih =>
      rw [isPerIndexQueryBound_query_bind_iff] at bound
      cases hs : seed i with
      | nil =>
          have hc := capacity i
          simp only [hs, List.length_nil] at hc
          omega
      | cons answer tail =>
          change p ∈ support ((simulateQ seededOracle (OracleComp.queryBind i next).withQueryLog).run seed) at hp
          rw [run_logged_query_cons i next seed answer tail hs] at hp
          rw [support_map] at hp
          obtain ⟨mid, hmid, rfl⟩ := hp
          have hc : ∀ j, Function.update budget i (budget i - 1) j ≤
              ((seed.update i tail) j).length := by
            intro j
            by_cases hj : j = i
            · subst j
              have h := capacity i
              simp only [hs, List.length_cons] at h
              simp only [Function.update_self, QuerySeed.update_self]
              omega
            · simpa only [Function.update_of_ne hj, QuerySeed.update_of_ne _ _ _ _ hj] using capacity j
          have hrest := ih answer _ (bound.2 answer) (seed.update i tail) hc mid hmid
          change (restore mid.1.2 mid.2).prependValues [answer] = seed
          rw [hrest]
          exact QuerySeed.eq_prependValues_of_pop_eq_some
            (QuerySeed.pop_eq_some_of_cons seed i answer tail hs)

end Signatures.Runtime.SeededTrace
