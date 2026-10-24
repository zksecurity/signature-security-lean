import Signatures.LinearFunctional.Spec.LazyAGMReduction
import Proofs.BLS.LazyAGMList

/-! Encountered-base cache invariants for weighted reduction phases. Existing
bindings are preserved, evaluated bases are cached, and rereading cached terms
does not allocate entries. No finite base-index or message domain is required. -/

open OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle privateListOracle_lookup privateListOracle_random)

namespace Model.LazyAGM.WeightedReduction

variable {F ι M R G₁ : Type} [DecidableEq ι] [SampleableType R]

/-- Every old binding is retained with its original answer. -/
def CacheExtends (before after : List (ι × R)) : Prop :=
  ∀ i r, before.lookup i = some r → after.lookup i = some r

omit [SampleableType R] in
theorem CacheExtends.refl (cache : List (ι × R)) : CacheExtends cache cache := fun _ _ h => h

omit [SampleableType R] in
theorem CacheExtends.trans {a b c : List (ι × R)}
    (hab : CacheExtends a b) (hbc : CacheExtends b c) : CacheExtends a c :=
  fun i r h => hbc i r (hab i r h)

def TermsCached (ts : List (ι × F)) (cache : List (ι × R)) : Prop :=
  ∀ p ∈ ts, ∃ r, cache.lookup p.1 = some r

omit [SampleableType R] in
theorem TermsCached.mono {ts : List (ι × F)} {before after : List (ι × R)}
    (h : TermsCached ts before) (he : CacheExtends before after) : TermsCached ts after := by
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  exact ⟨r, he _ _ hr⟩

theorem listLookup_preserves (i : ι) (cache : List (ι × R)) (z : R × List (ι × R))
    (hz : z ∈ support ((privateListOracle (.inr i)).run cache)) :
    CacheExtends cache z.2 ∧ z.2.lookup i = some z.1 ∧ z.2.length ≤ cache.length + 1 := by
  rw [privateListOracle_lookup] at hz
  cases h : cache.lookup i with
  | some r =>
      simp only [h, mem_support_pure_iff] at hz
      subst z
      exact ⟨CacheExtends.refl cache, h, by simp⟩
  | none =>
      simp only [h, support_map, Set.mem_image] at hz
      obtain ⟨r, _, rfl⟩ := hz
      refine ⟨?_, by simp, by simp⟩
      intro j s hj
      have hji : j ≠ i := by
        intro he
        subst j
        simp [h] at hj
      simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr hji] using hj

variable [AddCommMonoid R] [SMul F R]

/-- Cached weighted evaluation is a pure computation: it performs no new draw
and returns the exact original list, including any shadowed entries. -/
theorem evalTerms_cached_eq (ts : List (ι × F)) (cache : List (ι × R))
    (hc : TermsCached ts cache) :
    (simulateQ privateListOracle (evalTerms ts)).run cache =
      pure ((ts.map fun p => p.2 • (cache.lookup p.1).getD 0).sum, cache) := by
  induction ts with
  | nil => simp [evalTerms]
  | cons p rest ih =>
      rcases p with ⟨i, c⟩
      obtain ⟨r, hr⟩ := hc (i, c) (by simp)
      simp only [evalTerms, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure]
      rw [privateListOracle_lookup, hr]
      simp only [pure_bind]
      rw [ih (fun p hp => hc p (List.mem_cons_of_mem _ hp))]
      simp [hr]

theorem evalTerms_list_preserves (ts : List (ι × F)) (cache : List (ι × R))
    (z : R × List (ι × R))
    (hz : z ∈ support ((simulateQ privateListOracle (evalTerms ts)).run cache)) :
    CacheExtends cache z.2 ∧ TermsCached ts z.2 ∧ z.2.length ≤ cache.length + ts.length := by
  induction ts generalizing cache z with
  | nil =>
      have he : z = (0, cache) := by simpa [evalTerms] using hz
      subst z
      exact ⟨CacheExtends.refl cache, by simp [TermsCached], by simp⟩
  | cons p rest ih =>
      simp only [evalTerms, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
      obtain ⟨mid, hmid, last, hlast, he⟩ := hz
      subst z
      obtain ⟨hm, hmkey, hmlen⟩ := listLookup_preserves p.1 cache mid hmid
      obtain ⟨hl, hlkeys, hllen⟩ := ih mid.2 last hlast
      refine ⟨hm.trans hl, ?_, ?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with he | ht
        · subst t
          exact ⟨mid.1, hl _ _ hmkey⟩
        · exact hlkeys t ht
      · simp only [List.length_cons]
        omega

/-- Extraction over known bases preserves the entire list, including order and
any supplied shadowed entries. It consumes no fresh scalar samples. -/
theorem evalTerms_cached (ts : List (ι × F)) (cache : List (ι × R))
    (hc : TermsCached ts cache) (z : R × List (ι × R))
    (hz : z ∈ support ((simulateQ privateListOracle (evalTerms ts)).run cache)) : z.2 = cache := by
  induction ts generalizing z with
  | nil => simpa [evalTerms] using congrArg Prod.snd (show z = (0, cache) by simpa [evalTerms] using hz)
  | cons p rest ih =>
      obtain ⟨r, hr⟩ := hc p (by simp)
      simp only [evalTerms, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
      obtain ⟨mid, hmid, last, hlast, he⟩ := hz
      rw [privateListOracle_lookup, hr] at hmid
      have hm : mid = (r, cache) := by simpa using hmid
      subst mid
      subst z
      exact ih (fun t ht => hc t (List.mem_cons_of_mem _ ht)) last hlast

/-- Every explicit hash and every internal base of a signed message is cached. -/
def TranscriptCached (terms : M → List (ι × F)) (tr : Transcript ι M G₁)
    (cache : List (ι × R)) : Prop :=
  (∀ p ∈ tr.1, ∃ r, cache.lookup p.1 = some r) ∧
    ∀ p ∈ tr.2, TermsCached (terms p.1) cache

omit [SampleableType R] [AddCommMonoid R] [SMul F R] in
theorem TranscriptCached.mono (terms : M → List (ι × F)) (tr : Transcript ι M G₁)
    {before after : List (ι × R)} (hc : TranscriptCached terms tr before)
    (he : CacheExtends before after) : TranscriptCached terms tr after := by
  constructor
  · intro p hp
    obtain ⟨r, hr⟩ := hc.1 p hp
    exact ⟨r, he _ _ hr⟩
  · intro p hp
    exact (hc.2 p hp).mono he

def hashQuery : (Nat ⊕ ι) ⊕ M → Bool
  | .inl (.inr _) => true
  | _ => false

def signingQuery : (Nat ⊕ ι) ⊕ M → Bool
  | .inr _ => true
  | _ => false

def stepEntries (length : Nat) : (Nat ⊕ ι) ⊕ M → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => length

theorem privateStep_cache (terms : M → List (ι × F)) (hash sign : R → G₁)
    (length : Nat) (hl : ∀ m, (terms m).length ≤ length)
    (q : (advSpec ι M G₁).Domain) (tr : Transcript ι M G₁) (cache : List (ι × R))
    (hc : TranscriptCached terms tr cache)
    (z : ((advSpec ι M G₁).Range q × Transcript ι M G₁) × List (ι × R))
    (hz : z ∈ support ((simulateQ privateListOracle
      ((privateOracle terms hash sign q).run tr)).run cache)) :
    TranscriptCached terms z.1.2 z.2 ∧ z.2.length ≤ cache.length + stepEntries length q := by
  rcases q with ((n | i) | m)
  · simp only [privateOracle, handler, StateT.run_mk, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨mid, hmid, rfl⟩ := hz
    rw [privateListOracle_random] at hmid
    simp only [support_map, Set.mem_image] at hmid
    obtain ⟨r, _, rfl⟩ := hmid
    exact ⟨hc, by simp [stepEntries]⟩
  · simp only [privateOracle, handler, StateT.run_mk, simulateQ_bind,
      simulateQ_map, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
      StateT.run_map, StateT.run_pure, support_map, Set.mem_image,
      mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨mid, hmid, rfl⟩ := hz
    obtain ⟨mid, hmid, rfl⟩ := hmid
    obtain ⟨he, hkey, hlen⟩ := listLookup_preserves i cache mid hmid
    have htr := hc.mono terms tr he
    refine ⟨⟨?_, htr.2⟩, hlen⟩
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact htr.1 p hp
    · have hp' : p = (i, hash mid.1) := by simpa using hp
      subst p
      exact ⟨mid.1, hkey⟩
  · simp only [privateOracle, handler, StateT.run_mk, simulateQ_bind,
      simulateQ_map, simulateQ_pure, StateT.run_bind, StateT.run_map, StateT.run_pure,
      support_map, Set.mem_image, mem_support_bind_iff, mem_support_pure_iff] at hz
    obtain ⟨mid, hmid, rfl⟩ := hz
    obtain ⟨mid, hmid, rfl⟩ := hmid
    obtain ⟨he, hkeys, hlen⟩ := evalTerms_list_preserves (terms m) cache mid hmid
    have htr := hc.mono terms tr he
    refine ⟨⟨htr.1, ?_⟩, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact htr.2 p hp
      · have hp' : p = (m, sign mid.1) := by simpa using hp
        subst p
        exact hkeys
    · dsimp only [stepEntries]
      have hm := hl m
      omega

/-- Only explicit hash calls and bases of signed messages can allocate during
the adversary phase. Private randomness adds no entries. -/
theorem privateSim_cache {α : Type}
    (terms : M → List (ι × F)) (hash sign : R → G₁)
    (length : Nat) (hl : ∀ m, (terms m).length ≤ length)
    (oa : OracleComp (advSpec ι M G₁) α) (tr : Transcript ι M G₁) (cache : List (ι × R))
    (hashes signatures : Nat)
    (hh : IsQueryBoundP oa (fun q => hashQuery q = true) hashes)
    (hs : IsQueryBoundP oa (fun q => signingQuery q = true) signatures)
    (hc : TranscriptCached terms tr cache)
    (z : (α × Transcript ι M G₁) × List (ι × R))
    (hz : z ∈ support ((simulateQ privateListOracle
      ((simulateQ (privateOracle terms hash sign) oa).run tr)).run cache)) :
    TranscriptCached terms z.1.2 z.2 ∧ z.2.length ≤ cache.length + hashes + length * signatures := by
  induction oa using OracleComp.inductionOn generalizing tr cache hashes signatures with
  | pure a =>
      have he : z = ((a, tr), cache) := by simpa using hz
      subst z
      exact ⟨hc, by dsimp only; omega⟩
  | query_bind q next ih =>
      rw [isQueryBoundP_query_bind_iff] at hh hs
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨mid, hmid, hz⟩ := hz
      have hm := privateStep_cache terms hash sign length hl q tr cache hc mid hmid
      have ht := ih mid.1.1 mid.1.2 mid.2 _ _ (hh.2 mid.1.1) (hs.2 mid.1.1) hm.1 hz
      refine ⟨ht.1, ?_⟩
      rcases q with ((n | i) | m) <;>
        simp only [hashQuery, signingQuery, stepEntries, Bool.false_eq_true, not_false_eq_true,
          true_or, not_true_eq_false, false_or, ite_false, ite_true, Nat.add_zero] at hh hs hm ht
      · omega
      · omega
      · have hsub : signatures - 1 + 1 = signatures := by omega
        have hmul := congrArg (fun n => length * n) hsub
        simp only [Nat.mul_add, Nat.mul_one] at hmul
        omega

theorem privateRun_cache {G₂ : Type}
    (terms : M → List (ι × F)) (hash sign : R → G₁)
    (length : Nat) (hl : ∀ m, (terms m).length ≤ length)
    (A : Adversary F ι M G₁ G₂) (pk : G₂) (hashes signatures : Nat)
    (hh : IsQueryBoundP (A.main pk) (fun q => hashQuery q = true) hashes)
    (hs : IsQueryBoundP (A.main pk) (fun q => signingQuery q = true) signatures)
    (z : (Output F M × Transcript ι M G₁) × List (ι × R))
    (hz : z ∈ support ((simulateQ privateListOracle (privateRun terms hash sign A pk)).run [])) :
    TranscriptCached terms z.1.2 z.2 ∧ z.2.length ≤ hashes + length * signatures := by
  simpa using privateSim_cache terms hash sign length hl (A.main pk) ([], []) [] hashes signatures
    hh hs (by simp [TranscriptCached]) z hz

omit [SampleableType R] [AddCommMonoid R] [SMul F R] in
theorem hashTerms_cached [Zero F] (coeff : List F) (tr : List (ι × G₁))
    (cache : List (ι × R)) (hc : ∀ p ∈ tr, ∃ r, cache.lookup p.1 = some r) :
    TermsCached (BLS.LazyAGM.Reduction.traceTerms coeff tr) cache := by
  intro p hp
  simp only [BLS.LazyAGM.Reduction.traceTerms, List.mapIdx_eq_ofFn, List.mem_ofFn] at hp
  obtain ⟨n, rfl⟩ := hp
  exact hc _ (List.getElem_mem _)

omit [SampleableType R] [AddCommMonoid R] [SMul F R] in
theorem signedTerms_cached [MulZeroOneClass F] (terms : M → List (ι × F))
    (coeff : List F) (tr : List (M × G₁)) (cache : List (ι × R))
    (hc : ∀ p ∈ tr, TermsCached (terms p.1) cache) :
    TermsCached (signedTerms terms coeff tr) cache := by
  intro p hp
  simp only [signedTerms, List.mem_flatten, List.mapIdx_eq_ofFn, List.mem_ofFn] at hp
  obtain ⟨ts, ⟨n, rfl⟩, hp⟩ := hp
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
  exact hc _ (List.getElem_mem _) t ht

end Model.LazyAGM.WeightedReduction
