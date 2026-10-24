import Proofs.LinearFunctional.LazyAGMCacheBound
import Proofs.OOPS.LazyAGMSecurity
import Proofs.Proximity.LazyAGMSecurity
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Model.LazyAGM Model.LazyAGM.WeightedReduction
open BLS.LazyAGM.Reduction (privateListOracle traceValue_eq_mapIdx)

namespace SignaturesTest.WeightedAGMReduction

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Index and message types differ, and both are infinite. A message uses two
-- adjacent bases; the false branch also exercises an empty weighted sum.
private def terms (m : Nat × Bool) : List (Nat × ZMod 5) :=
  if m.2 then [(m.1, 1), (m.1 + 1, 2)] else []

private def output : Output (ZMod 5) (Nat × Bool) := ⟨(99, true), 1, [2, 4, 3], [3]⟩

private def signFirst : Adversary (ZMod 5) Nat (Nat × Bool) (ZMod 5) (ZMod 5) where
  main _ := do
    let _ : ZMod 5 ← liftM ((advSpec Nat (Nat × Bool) (ZMod 5)).query (.inr (7, true)))
    let _ : ZMod 5 ← liftM ((advSpec Nat (Nat × Bool) (ZMod 5)).query (.inl (.inr 7)))
    let _ : ZMod 5 ← liftM ((advSpec Nat (Nat × Bool) (ZMod 5)).query (.inl (.inr 7)))
    let _ : ZMod 5 ← liftM ((advSpec Nat (Nat × Bool) (ZMod 5)).query (.inr (7, true)))
    pure output

-- Repeated signing occurrences stay separate. The missing second coefficient
-- is zero; an extra coefficient without a reply does not generate any terms.
example : signedTerms terms [3] [((7, true), (0 : ZMod 5)), ((7, true), 0)] =
    [(7, 3), (8, 1), (7, 0), (8, 0)] := by decide

example : signedTerms terms [3, 4] [((7, true), (0 : ZMod 5))] = [(7, 3), (8, 1)] := by decide

example : simulateQ (BLS.CoCDH.coinTableImpl (fun i : Nat => if i = 7 then (2 : ZMod 5) else 4))
    (goodProgram terms 1 3 3 signFirst) = pure 4 := by
  rw [goodProgram_table]
  simp [fixedRun, fixedImpl, handler, signFirst, output, traceValue_eq_mapIdx,
    termsValue, terms, tokenCoeff]
  apply (div_eq_iff (by decide)).2
  decide

example : simulateQ (BLS.CoCDH.coinTableImpl
    (fun i : Nat => if i = 7 then ((2, 1) : ZMod 5 × ZMod 5) else (4, 3)))
    (badProgram terms 1 3 2 2 signFirst) = pure 1 := by
  rw [badProgram_table]
  simp [fixedRun, fixedImpl, handler, signFirst, output, traceValue_eq_mapIdx,
    termsValue, terms, tokenCoeff]
  apply (div_eq_iff (by decide)).2
  decide

example : simulateQ (BLS.CoCDH.coinTableImpl (fun _ : Nat => (0 : ZMod 5)))
    (goodProgram terms 1 3 3 signFirst) = pure 0 := by
  rw [goodProgram_table]
  simp [fixedRun, fixedImpl, handler, signFirst, output, traceValue_eq_mapIdx,
    termsValue, terms, tokenCoeff]

example : simulateQ (BLS.CoCDH.coinTableImpl (fun _ : Nat => ((0, 1) : ZMod 5 × ZMod 5)))
    (badProgram terms 1 3 2 2 signFirst) = pure 0 := by
  rw [badProgram_table]
  simp [fixedRun, fixedImpl, handler, signFirst, output, traceValue_eq_mapIdx,
    termsValue, terms, tokenCoeff]

-- An extracted weighted sum rereads existing entries, preserving the cache
-- exactly and making no sampling request, even with a shadowed key.
example : (simulateQ privateListOracle (evalTerms (terms (7, true)))).run
    [(7, (2 : ZMod 5)), (8, 4), (7, 1)] = pure (0, [(7, 2), (8, 4), (7, 1)]) := by
  rw [evalTerms_cached_eq _ _ (by simp [TermsCached, terms]; decide)]
  congr 1

example : (simulateQ privateListOracle (evalTerms (G₁ := ZMod 5) (terms (7, false)))).run [] =
    pure (0, []) := rfl

private def adaptive : Adversary (ZMod 5) Nat (Nat × Bool) (ZMod 5) (ZMod 5) where
  main _ := do
    let bit : Fin 2 ← liftM ((advSpec Nat (Nat × Bool) (ZMod 5)).query (.inl (.inl 1)))
    let signed : ZMod 5 ← liftM ((advSpec Nat (Nat × Bool) (ZMod 5)).query (.inr (bit.val, true)))
    let _ : ZMod 5 ← liftM ((advSpec Nat (Nat × Bool) (ZMod 5)).query (.inl (.inr signed.val)))
    pure ⟨(signed.val + 10, true), 1, [2], [3]⟩

example (table : Nat → ZMod 5) :
    simulateQ (BLS.CoCDH.coinTableImpl table) (privateRun terms id (fun r => 2 * r) adaptive 2) =
      fixedRun adaptive 2 table (fun m => 2 * termsValue terms table m) :=
  privateRun_table terms table _ _ adaptive 2

-- The random branch and the returned signature choose later indices. A private
-- random request consumes no cache capacity; this bound holds for every outcome.
example (z : ZMod 5 × List (Nat × ZMod 5))
    (hz : z ∈ support ((simulateQ privateListOracle (goodProgram terms 1 3 3 adaptive)).run [])) :
    z.2.length ≤ 5 := by
  apply goodProgram_cache_bound terms 2 (by intro m; simp [terms]; split <;> simp)
    1 3 3 adaptive 1 1 ?_ ?_ z hz
  all_goals simp [adaptive, isQueryBoundP_query_bind_iff, hashQuery, signingQuery]

example (z : ZMod 5 × List (Nat × ZMod 5))
    (hz : z ∈ support ((simulateQ privateListOracle (goodProgram terms 1 3 3 signFirst)).run [])) :
    z.2.length ≤ 8 := by
  apply goodProgram_cache_bound terms 2 (by intro m; simp [terms]; split <;> simp)
    1 3 3 signFirst 2 2 ?_ ?_ z hz
  all_goals simp [signFirst, isQueryBoundP_query_bind_iff, hashQuery, signingQuery]

example (z : ZMod 5 × List (Nat × (ZMod 5 × ZMod 5)))
    (hz : z ∈ support ((simulateQ privateListOracle (badProgram terms 1 3 2 2 signFirst)).run [])) :
    z.2.length ≤ 8 := by
  apply badProgram_cache_bound terms 2 (by intro m; simp [terms]; split <;> simp)
    1 3 2 2 signFirst 2 2 ?_ ?_ z hz
  all_goals simp [signFirst, isQueryBoundP_query_bind_iff, hashQuery, signingQuery]

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``signedTerms_value, ``denominatorCoeff_value, ``goodProgram_table, ``badProgram_table,
      ``goodReductionLazy_eq_eager, ``badReductionLazy_eq_eager,
      ``goodReductionList_eq, ``badReductionList_eq, ``goodAdvantage_eq_eager, ``badAdvantage_eq_eager,
      ``evalTerms_cached_eq, ``privateRun_cache, ``goodProgram_cache_bound, ``badProgram_cache_bound,
      ``OOPS.LazyAGM.Proofs.security_lazy_finite_topics,
      ``Proximity.LazyAGM.Proofs.security_lazy_finite_slots] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``goodReductionLazy, ``badReductionLazy, ``goodReductionList, ``badReductionList,
      ``privateRun_table, ``goodProgram_table, ``badProgram_table,
      ``goodReductionList_eq, ``badReductionList_eq, ``privateRun_cache,
      ``goodProgram_cache_bound, ``badProgram_cache_bound] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          if let .fvar id := type.getAppArgs[0]! then
            if #[`ι, `M, `G₂].contains (← id.getUserName) then
              throwError "{name}: finite-domain requirement on lazy execution"

end SignaturesTest.WeightedAGMReduction
