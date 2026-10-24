import Proofs.Runtime.WeightedExecution

/-! Every completed weighted interaction leaves the bases of every explicit
reply in its private cache. The invariant follows all adaptive replies and
preserves existing lookup answers, including in caches containing shadowed entries. It needs neither
a finite index/message domain nor a quantitative bound on the source program. -/

open OracleComp OracleSpec Model.LazyAGM Model.LazyAGM.WeightedReduction

namespace Signatures.Runtime.WeightedAGM

open Reply

variable {F ι M R G₁ α : Type} [DecidableEq ι] [SampleableType R]
  [AddCommMonoid R] [SMul F R]

theorem listOracle_cached (terms : M → List (ι × F)) (hash sign : R → G₁)
    (q : (advSpec ι M G₁).Domain) (state : State ι M R G₁)
    (hc : TranscriptCached terms (chronological state.2) state.1)
    (z : (advSpec ι M G₁).Range q × State ι M R G₁)
    (hz : z ∈ support (((listOracle terms hash sign) q).run state)) :
    CacheExtends state.1 z.2.1 ∧ TranscriptCached terms (chronological z.2.2) z.2.1 := by
  rcases q with (n | i) | m
  · rw [listOracle_random] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨r, _, rfl⟩ := hz
    exact ⟨.refl _, hc⟩
  · rw [listOracle_hash] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    obtain ⟨he, hkey, _⟩ := listLookup_preserves i state.1 p hp
    have htr := hc.mono terms (chronological state.2) he
    rw [chronological_record]
    refine ⟨he, ⟨?_, htr.2⟩⟩
    intro entry hm
    rcases List.mem_append.mp hm with hm | hm
    · exact htr.1 entry hm
    · have heq : entry = (i, hash p.1) := by simpa only [List.mem_singleton] using hm
      subst entry
      exact ⟨p.1, hkey⟩
  · rw [listOracle_sign] at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    obtain ⟨he, hkeys, _⟩ := evalTerms_list_preserves (terms m) state.1 p hp
    have htr := hc.mono terms (chronological state.2) he
    rw [chronological_record]
    refine ⟨he, ⟨htr.1, ?_⟩⟩
    intro entry hm
    rcases List.mem_append.mp hm with hm | hm
    · exact htr.2 entry hm
    · have heq : entry = (m, sign p.1) := by simpa only [List.mem_singleton] using hm
      subst entry
      exact hkeys

theorem listSimulation_cached (terms : M → List (ι × F)) (hash sign : R → G₁)
    (oa : OracleComp (advSpec ι M G₁) α) (state : State ι M R G₁)
    (hc : TranscriptCached terms (chronological state.2) state.1)
    (z : α × State ι M R G₁)
    (hz : z ∈ support ((simulateQ (listOracle terms hash sign) oa).run state)) :
    CacheExtends state.1 z.2.1 ∧ TranscriptCached terms (chronological z.2.2) z.2.1 := by
  induction oa using OracleComp.inductionOn generalizing state with
  | pure a =>
      have he : z = (a, state) := by simpa using hz
      subst z
      exact ⟨.refl _, hc⟩
  | query_bind q next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨mid, hmid, hz⟩ := hz
      have hm := listOracle_cached terms hash sign q state hc mid hmid
      have ht := ih mid.1 mid.2 hm.2 hz
      exact ⟨hm.1.trans ht.1, ht.2⟩

end Signatures.Runtime.WeightedAGM
