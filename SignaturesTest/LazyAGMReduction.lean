import Proofs.BLS.LazyAGMSecurity
import Proofs.BLS.LazyAGMList
import Proofs.BLS.LazyAGMCacheBound
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Model.LazyAGM BLS.LazyAGM.Reduction
open Model.LazyAGM.WeightedReduction (hashQuery signingQuery)

namespace SignaturesTest.LazyAGMReduction

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def output : Output (ZMod 5) Nat := ⟨99, 1, [2, 4, 3], [3]⟩

-- Signing first and then hashing the same key twice produces three visible
-- occurrences. The extra hash coefficient has no received token.
private def signFirst : Adversary (ZMod 5) Nat Nat (ZMod 5) (ZMod 5) where
  main _ := do
    let _ : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inr 7))
    let _ : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inl (.inr 7)))
    let _ : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inl (.inr 7)))
    pure output

example : traceValue ([2, 4, 3] : List (ZMod 5))
    [(7, (2 : ZMod 5)), (7, 2)] (fun _ : Nat => (2 : ZMod 5)) = 2 := by
  decide

example : traceValue ([2] : List (ZMod 5))
    [(7, (2 : ZMod 5)), (8, 4)] (fun m : Nat => (m : ZMod 5)) = 4 := by
  decide

-- This deterministic interpretation checks the unseen final target, sparse
-- numerator, repeated-message denominator, and zero-extension of coefficients.
example : simulateQ (BLS.CoCDH.coinTableImpl (fun m : Nat => if m = 7 then (2 : ZMod 5) else 4))
    (goodProgram 1 3 3 signFirst) = pure 1 := by
  rw [goodProgram_table]
  simp [fixedRun, fixedImpl, handler, signFirst, output, traceValue_eq_mapIdx, tokenCoeff]
  apply (div_eq_iff (by decide)).2
  decide

example : simulateQ (BLS.CoCDH.coinTableImpl
    (fun m : Nat => if m = 7 then ((2, 1) : ZMod 5 × ZMod 5) else (4, 4)))
    (badProgram 1 3 2 2 signFirst) = pure 3 := by
  rw [badProgram_table]
  simp [fixedRun, fixedImpl, handler, signFirst, output, traceValue_eq_mapIdx, tokenCoeff]
  apply (div_eq_iff (by decide)).2
  decide

-- A zero denominator returns zero under the source field-division convention.
example : simulateQ (BLS.CoCDH.coinTableImpl (fun _ : Nat => (0 : ZMod 5)))
    (goodProgram 1 3 3 signFirst) = pure 0 := by
  rw [goodProgram_table]
  simp [fixedRun, fixedImpl, handler, signFirst, output, traceValue_eq_mapIdx, tokenCoeff]

example : simulateQ (BLS.CoCDH.coinTableImpl (fun _ : Nat => ((0, 1) : ZMod 5 × ZMod 5)))
    (badProgram 1 3 2 2 signFirst) = pure 0 := by
  rw [badProgram_table]
  simp [fixedRun, fixedImpl, handler, signFirst, output, traceValue_eq_mapIdx, tokenCoeff]

-- Private randomness and returned signatures can choose later requests. The
-- fixed-table theorem retains that complete adaptive computation.
private def adaptive : Adversary (ZMod 5) Nat Nat (ZMod 5) (ZMod 5) where
  main _ := do
    let bit : Fin 2 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inl (.inl 1)))
    let signed : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inr bit.val))
    let _ : ZMod 5 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inl (.inr signed.val)))
    pure ⟨signed.val + 10, 1, [2], [3]⟩

example (rho : Nat → ZMod 5) :
    simulateQ (BLS.CoCDH.coinTableImpl rho) (privateRun (fun r => r) (fun r => 2 * r) adaptive 2) =
      fixedRun adaptive 2 rho (fun m => 2 * rho m) :=
  privateRun_table rho _ _ adaptive 2

-- An actual cache hit executes no new draw, even over the infinite Nat domain.
example (cache : (Nat →ₒ ZMod 5).QueryCache) (h : cache 7 = some 2) :
    ((BLS.CoCDH.lazyCoinImpl (D := Nat) (R := ZMod 5)) (.inr 7)).run cache =
      pure ((2 : ZMod 5), cache) := by
  exact QueryImpl.withCaching_run_some _ h

example : IsTotalQueryBound (goodProgram 1 3 3 signFirst) 7 := by
  apply goodProgram_queries (q := 3)
  simp [signFirst, IsTotalQueryBound]

example : IsTotalQueryBound (badProgram 1 3 2 2 signFirst) 7 := by
  apply badProgram_queries (q := 3)
  simp [signFirst, IsTotalQueryBound]

-- The sharper bound counts hash/sign requests, including repeated calls, rather
-- than extraction rereads. It applies to every supported output/cache pair.
example (z : ZMod 5 × List (Nat × ZMod 5))
    (hz : z ∈ support ((simulateQ privateListOracle (goodProgram 1 3 3 signFirst)).run [])) :
    z.2.length ≤ 4 := by
  apply goodList_cache_bound_by_kind 1 3 3 signFirst 2 1 ?_ ?_ z hz
  all_goals simp [signFirst, isQueryBoundP_query_bind_iff, hashQuery, signingQuery]

example (z : ZMod 5 × List (Nat × (ZMod 5 × ZMod 5)))
    (hz : z ∈ support ((simulateQ privateListOracle (badProgram 1 3 2 2 signFirst)).run [])) :
    z.2.length ≤ 4 := by
  apply badList_cache_bound_by_kind 1 3 2 2 signFirst 2 1 ?_ ?_ z hz
  all_goals simp [signFirst, isQueryBoundP_query_bind_iff, hashQuery, signingQuery]

-- Private randomness and an oracle reply choose later messages. The private
-- random query consumes no cache entry in either branch.
example (z : ZMod 5 × List (Nat × ZMod 5))
    (hz : z ∈ support ((simulateQ privateListOracle (goodProgram 1 3 3 adaptive)).run [])) :
    z.2.length ≤ 3 := by
  apply goodList_cache_bound_by_kind 1 3 3 adaptive 1 1 ?_ ?_ z hz
  all_goals simp [adaptive, isQueryBoundP_query_bind_iff, hashQuery, signingQuery]

example (z : ZMod 5 × List (Nat × (ZMod 5 × ZMod 5)))
    (hz : z ∈ support ((simulateQ privateListOracle (badProgram 1 3 2 2 adaptive)).run [])) :
    z.2.length ≤ 3 := by
  apply badList_cache_bound_by_kind 1 3 2 2 adaptive 1 1 ?_ ?_ z hz
  all_goals simp [adaptive, isQueryBoundP_query_bind_iff, hashQuery, signingQuery]

private def randomOnly : Adversary (ZMod 5) Nat Nat (ZMod 5) (ZMod 5) where
  main _ := do
    let index : Fin 1000001 ← liftM ((advSpec Nat Nat (ZMod 5)).query (.inl (.inl 1000000)))
    pure ⟨index.val, 1, [], []⟩

-- With zero hash/sign allowances, even a large private range leaves room for
-- only the final target. The message domain remains the infinite type Nat.
example (z : ZMod 5 × List (Nat × ZMod 5))
    (hz : z ∈ support ((simulateQ privateListOracle (goodProgram 1 3 3 randomOnly)).run [])) :
    z.2.length ≤ 1 := by
  apply goodList_cache_bound_by_kind 1 3 3 randomOnly 0 0 ?_ ?_ z hz
  all_goals simp [randomOnly, hashQuery, signingQuery]

example (z : ZMod 5 × List (Nat × (ZMod 5 × ZMod 5)))
    (hz : z ∈ support ((simulateQ privateListOracle (badProgram 1 3 2 2 randomOnly)).run [])) :
    z.2.length ≤ 1 := by
  apply badList_cache_bound_by_kind 1 3 2 2 randomOnly 0 0 ?_ ?_ z hz
  all_goals simp [randomOnly, hashQuery, signingQuery]

-- First bindings win even for a supplied cache with duplicate keys.
example : ((privateListOracle (M := Nat) (R := ZMod 5)) (.inr 7)).run [(7, 2), (7, 4)] =
    pure ((2 : ZMod 5), [(7, 2), (7, 4)]) := by
  rw [privateListOracle_lookup]
  rfl

private def repeatedProbe : OracleComp (baseSpec Nat (ZMod 5)) (ZMod 5 × ZMod 5 × ZMod 5 × ZMod 5) := do
  let first ← (liftM ((baseSpec Nat (ZMod 5)).query (.inr 7)) : OracleComp (baseSpec Nat (ZMod 5)) (ZMod 5))
  let repeated ← (liftM ((baseSpec Nat (ZMod 5)).query (.inr 7)) : OracleComp (baseSpec Nat (ZMod 5)) (ZMod 5))
  let target ← (liftM ((baseSpec Nat (ZMod 5)).query (.inr 99)) : OracleComp (baseSpec Nat (ZMod 5)) (ZMod 5))
  let targetAgain ← (liftM ((baseSpec Nat (ZMod 5)).query (.inr 99)) : OracleComp (baseSpec Nat (ZMod 5)) (ZMod 5))
  pure (first, repeated, target, targetAgain)

-- Four requests, two distinct messages, exactly two draws and two stored cells.
example : (simulateQ privateListOracle repeatedProbe).run [] = (do
    let first ← ($ᵗ (ZMod 5) : ProbComp (ZMod 5))
    let target ← ($ᵗ (ZMod 5) : ProbComp (ZMod 5))
    pure ((first, first, target, target), [(99, target), (7, first)])) := by
  simp only [repeatedProbe, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  erw [privateListOracle_lookup]
  simp only [List.lookup_nil, bind_map_left]
  apply bind_congr
  intro first
  erw [privateListOracle_lookup]
  simp only [List.lookup_cons_self, pure_bind]
  erw [privateListOracle_lookup]
  simp only [List.lookup_cons, show ((99 : Nat) == 7) = false from rfl,
    List.lookup_nil, bind_map_left]
  apply bind_congr
  intro target
  erw [privateListOracle_lookup]
  simp

open Lean Meta Elab Command

run_cmd liftTermElabM do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``privateRun_table, ``evalTerms_table, ``goodProgram_table, ``badProgram_table,
      ``traceValue_eq_mapIdx, ``traceValue_fst, ``traceValue_snd, ``baseCoeff_traceValue,
      ``denominatorCoeff_traceValue, ``lazyRun_eq_table, ``maskTable_bind,
      ``goodReductionLazy_eq_eager, ``badReductionLazy_eq_eager,
      ``goodAdvantage_eq_eager, ``badAdvantage_eq_eager, ``security_finite_messages,
      ``privateSim_queries, ``privateSim_transcript, ``privateRun_queries,
      ``privateRun_transcript, ``evalTerms_queries, ``goodProgram_queries, ``badProgram_queries,
      ``privateListOracle_projection, ``privateListRun_projection, ``privateListRun_erase,
      ``privateListOracle_growth, ``privateListRun_growth, ``goodReductionList_eq,
      ``badReductionList_eq, ``goodList_cache_bound, ``badList_cache_bound,
      ``weighted_goodProgram_eq, ``weighted_badProgram_eq,
      ``goodList_cache_bound_by_kind, ``badList_cache_bound_by_kind] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``goodReductionLazy, ``badReductionLazy, ``privateRun_table,
      ``goodProgram_table, ``badProgram_table, ``traceValue_eq_mapIdx,
      ``goodReductionList, ``badReductionList, ``privateListRun_projection,
      ``goodProgram_queries, ``badProgram_queries, ``goodList_cache_bound, ``badList_cache_bound,
      ``weighted_goodProgram_eq, ``weighted_badProgram_eq,
      ``goodList_cache_bound_by_kind, ``badList_cache_bound_by_kind] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          if let .fvar id := type.getAppArgs[0]! then
            if (← id.getUserName) == `M then
              throwError "{name}: added a finite-message assumption to a lazy solver"

end SignaturesTest.LazyAGMReduction
