import Signatures.BLS.Spec.LazyAGMList
import Signatures.BLS.Proofs.LazyAGMQueries

/-! Exact adaptive cache-representation refinement and entry-count bounds.
Neither the list interpreter nor these proofs enumerate the message domain. -/

open OracleComp OracleSpec Model.LazyAGM

namespace BLS.LazyAGM.Reduction

variable {F M R G₁ G₂ α : Type} [DecidableEq M] [SampleableType R]

theorem privateListOracle_random (n : Nat) (cache : List (M × R)) :
    ((privateListOracle (M := M) (R := R)) (.inl n)).run cache =
      (fun r => (r, cache)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))) := rfl

theorem privateListOracle_lookup (m : M) (cache : List (M × R)) :
    ((privateListOracle (M := M) (R := R)) (.inr m)).run cache =
      (match cache.lookup m with
        | some r => pure (r, cache)
        | none => (fun r => (r, (m, r) :: cache)) <$> ($ᵗ R : ProbComp R)) := rfl

theorem privateListOracle_projection (q : (baseSpec M R).Domain) (cache : List (M × R)) :
    Prod.map id QueryImpl.ListCache.decode <$> (privateListOracle q).run cache =
      (CoCDH.lazyCoinImpl q).run (QueryImpl.ListCache.decode cache) := by
  rcases q with n | m
  · change Prod.map id QueryImpl.ListCache.decode <$>
      ((fun r => (r, cache)) <$> (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))) =
        (fun r => (r, QueryImpl.ListCache.decode cache)) <$>
          (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
    simp only [Functor.map_map, Prod.map_apply, id_eq]
  · exact QueryImpl.ListCache.local_projection _ m cache

theorem privateListRun_projection (oa : OracleComp (baseSpec M R) α) (cache : List (M × R)) :
    Prod.map id QueryImpl.ListCache.decode <$> (simulateQ privateListOracle oa).run cache =
      (simulateQ CoCDH.lazyCoinImpl oa).run (QueryImpl.ListCache.decode cache) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ QueryImpl.ListCache.decode
    privateListOracle_projection oa cache

theorem privateListRun_erase (oa : OracleComp (baseSpec M R) α) (cache : List (M × R)) :
    (simulateQ privateListOracle oa).run' cache =
      (simulateQ CoCDH.lazyCoinImpl oa).run' (QueryImpl.ListCache.decode cache) := by
  have h := congrArg (fun comp => Prod.fst <$> comp) (privateListRun_projection oa cache)
  simpa only [StateT.run'_eq, Functor.map_map, Function.comp_def, Prod.map_fst, id_eq] using h

theorem privateListOracle_growth (q : (baseSpec M R).Domain) (cache : List (M × R))
    (z : (baseSpec M R).Range q × List (M × R))
    (hz : z ∈ support ((privateListOracle q).run cache)) :
    z.2.length ≤ cache.length + 1 := by
  rcases q with n | m
  · change z ∈ support ((fun r => (r, cache)) <$>
      (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨r, _, rfl⟩ := hz
    simp
  · change z ∈ support (QueryImpl.ListCache.handler uniformSampleImpl m cache) at hz
    unfold QueryImpl.ListCache.handler at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst z
      simp
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨r, _, rfl⟩ := hz
      simp

theorem privateListRun_growth (oa : OracleComp (baseSpec M R) α) (cache : List (M × R))
    (q : Nat) (hq : IsTotalQueryBound oa q) (z : α × List (M × R))
    (hz : z ∈ support ((simulateQ privateListOracle oa).run cache)) :
    z.2.length ≤ cache.length + q := by
  induction oa using OracleComp.inductionOn generalizing q cache with
  | pure a =>
    have he : z = (a, cache) := by simpa using hz
    subst z
    simp
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hz
    obtain ⟨mid, hmid, hz⟩ := hz
    have hg := privateListOracle_growth query cache mid hmid
    have ht := ih mid.1 mid.2 (q - 1) (hq.2 mid.1) hz
    omega

omit [SampleableType R] in
theorem goodReductionList_eq [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] (A : Adversary F M M G₁ G₂) :
    goodReductionList A = goodReductionLazy A := by
  funext g X g₂ pk
  unfold goodReductionList goodReductionLazy
  rw [privateListRun_erase, QueryImpl.ListCache.decode_nil]

omit [SampleableType R] in
theorem badReductionList_eq [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (A : Adversary F M M G₁ G₂) :
    badReductionList A = badReductionLazy A := by
  funext g X g₂ pk
  unfold badReductionList badReductionLazy
  apply bind_congr
  intro kappa
  rw [privateListRun_erase, QueryImpl.ListCache.decode_nil]

omit [SampleableType R] in
theorem goodList_cache_bound [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] (g X : G₁) (pk : G₂)
    (A : Adversary F M M G₁ G₂) (q : Nat) (hq : IsTotalQueryBound (A.main pk) q)
    (z : F × List (M × F))
    (hz : z ∈ support ((simulateQ privateListOracle (goodProgram g X pk A)).run [])) :
    z.2.length ≤ 2 * q + 1 := by
  simpa using privateListRun_growth (goodProgram g X pk A) [] (2 * q + 1)
    (goodProgram_queries g X pk A q hq) z hz

omit [SampleableType R] in
theorem badList_cache_bound [Field F] [SampleableType F]
    [AddCommGroup G₁] [Module F G₁] (g X : G₁) (pk : G₂) (kappa : F)
    (A : Adversary F M M G₁ G₂) (q : Nat) (hq : IsTotalQueryBound (A.main pk) q)
    (z : F × List (M × (F × F)))
    (hz : z ∈ support ((simulateQ privateListOracle (badProgram g X pk kappa A)).run [])) :
    z.2.length ≤ 2 * q + 1 := by
  simpa using privateListRun_growth (badProgram g X pk kappa A) [] (2 * q + 1)
    (badProgram_queries g X pk kappa A q hq) z hz

end BLS.LazyAGM.Reduction
