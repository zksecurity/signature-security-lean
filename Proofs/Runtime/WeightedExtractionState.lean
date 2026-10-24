import Proofs.Runtime.WeightedExtraction
import Proofs.Runtime.BackendLazyAGMExtractionState
import Proofs.LinearFunctional.LazyAGMCache

/-! Transcript extraction rereads cached bases. Only final-target evaluation
can allocate entries. These laws retain the whole cache, including shadowed
bindings; they do not replace the executable scans by free semantic operations. -/

open OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)
open Model.LazyAGM.WeightedReduction

namespace Signatures.Runtime.WeightedAGM.Extract

variable {F ι M R G : Type} [DecidableEq ι]

/-- Proof-side value of a fully cached ordered term list. -/
def cachedValue [AddCommMonoid R] [SMul F R] (rows : List (ι × F)) (cache : List (ι × R)) : R :=
  (rows.map fun row => row.2 • (cache.lookup row.1).getD 0).sum

variable [Field F] [SampleableType F]

theorem goodFinish_cachedTranscript (terms : M → List (ι × F))
    (out : Model.LazyAGM.Output F M) (tr : Model.LazyAGM.Transcript ι M G)
    (cache : List (ι × F)) (hc : TranscriptCached terms tr cache) :
    (simulateQ (privateListOracle (M := ι) (R := F)) (goodFinish terms out tr)).run cache =
      (fun p => ((out.β + cachedValue (BLS.LazyAGM.Reduction.traceTerms out.γ tr.1) cache) /
        (p.1 - cachedValue (signedTerms terms out.ξ tr.2) cache), p.2)) <$>
          (simulateQ (privateListOracle (M := ι) (R := F)) (evalTerms (terms out.mstar))).run cache := by
  simp only [goodFinish, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [evalTerms_cached_eq _ cache (hashTerms_cached out.γ tr.1 cache hc.1)]
  simp only [pure_bind]
  rw [evalTerms_cached_eq _ cache (signedTerms_cached terms out.ξ tr.2 cache hc.2)]
  simp only [pure_bind, bind_pure_comp, cachedValue]

theorem badFinish_cachedTranscript (terms : M → List (ι × F))
    (out : Model.LazyAGM.Output F M) (tr : Model.LazyAGM.Transcript ι M G)
    (cache : List (ι × (F × F))) (hc : TranscriptCached terms tr cache) :
    (simulateQ (privateListOracle (M := ι) (R := F × F)) (badFinish terms out tr)).run cache =
      (fun p => (-(p.1.2 - (cachedValue (signedTerms terms out.ξ tr.2) cache).2) /
        (p.1.1 - (cachedValue (signedTerms terms out.ξ tr.2) cache).1), p.2)) <$>
          (simulateQ (privateListOracle (M := ι) (R := F × F)) (evalTerms (terms out.mstar))).run cache := by
  simp only [badFinish, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [evalTerms_cached_eq _ cache (signedTerms_cached terms out.ξ tr.2 cache hc.2)]
  simp only [pure_bind, bind_pure_comp, cachedValue]

theorem goodFinish_cached (terms : M → List (ι × F))
    (out : Model.LazyAGM.Output F M) (tr : Model.LazyAGM.Transcript ι M G)
    (cache : List (ι × F)) (hc : TranscriptCached terms tr cache)
    (ht : TermsCached (terms out.mstar) cache) :
    (simulateQ (privateListOracle (M := ι) (R := F)) (goodFinish terms out tr)).run cache =
      pure ((out.β + cachedValue (BLS.LazyAGM.Reduction.traceTerms out.γ tr.1) cache) /
        (cachedValue (terms out.mstar) cache - cachedValue (signedTerms terms out.ξ tr.2) cache), cache) := by
  rw [goodFinish_cachedTranscript terms out tr cache hc, evalTerms_cached_eq _ cache ht, map_pure]
  rfl

theorem badFinish_cached (terms : M → List (ι × F))
    (out : Model.LazyAGM.Output F M) (tr : Model.LazyAGM.Transcript ι M G)
    (cache : List (ι × (F × F))) (hc : TranscriptCached terms tr cache)
    (ht : TermsCached (terms out.mstar) cache) :
    (simulateQ (privateListOracle (M := ι) (R := F × F)) (badFinish terms out tr)).run cache =
      pure (-((cachedValue (terms out.mstar) cache).2 - (cachedValue (signedTerms terms out.ξ tr.2) cache).2) /
        ((cachedValue (terms out.mstar) cache).1 - (cachedValue (signedTerms terms out.ξ tr.2) cache).1), cache) := by
  rw [badFinish_cachedTranscript terms out tr cache hc, evalTerms_cached_eq _ cache ht, map_pure]
  rfl

theorem goodFinish_cache (p : ι → Prop) (terms : M → List (ι × F))
    (out : Model.LazyAGM.Output F M) (tr : Model.LazyAGM.Transcript ι M G)
    (cache : List (ι × F)) (hc : TranscriptCached terms tr cache)
    (hk : ∀ entry ∈ cache, p entry.1) (ht : ∀ row ∈ terms out.mstar, p row.1)
    (z : F × List (ι × F))
    (hz : z ∈ support ((simulateQ (privateListOracle (M := ι) (R := F))
      (goodFinish terms out tr)).run cache)) :
    CacheExtends cache z.2 ∧ TermsCached (terms out.mstar) z.2 ∧
      z.2.length ≤ cache.length + (terms out.mstar).length ∧ ∀ entry ∈ z.2, p entry.1 := by
  rw [goodFinish_cachedTranscript terms out tr cache hc] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨target, htarget, rfl⟩ := hz
  obtain ⟨he, hcached, hlength⟩ := evalTerms_list_preserves (terms out.mstar) cache target htarget
  exact ⟨he, hcached, hlength, LazyAGM.privateTerms_messages p (terms out.mstar) cache ht hk target htarget⟩

theorem badFinish_cache (p : ι → Prop) (terms : M → List (ι × F))
    (out : Model.LazyAGM.Output F M) (tr : Model.LazyAGM.Transcript ι M G)
    (cache : List (ι × (F × F))) (hc : TranscriptCached terms tr cache)
    (hk : ∀ entry ∈ cache, p entry.1) (ht : ∀ row ∈ terms out.mstar, p row.1)
    (z : F × List (ι × (F × F)))
    (hz : z ∈ support ((simulateQ (privateListOracle (M := ι) (R := F × F))
      (badFinish terms out tr)).run cache)) :
    CacheExtends cache z.2 ∧ TermsCached (terms out.mstar) z.2 ∧
      z.2.length ≤ cache.length + (terms out.mstar).length ∧ ∀ entry ∈ z.2, p entry.1 := by
  rw [badFinish_cachedTranscript terms out tr cache hc] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨target, htarget, rfl⟩ := hz
  obtain ⟨he, hcached, hlength⟩ := evalTerms_list_preserves (terms out.mstar) cache target htarget
  exact ⟨he, hcached, hlength, LazyAGM.privateTerms_messages p (terms out.mstar) cache ht hk target htarget⟩

end Signatures.Runtime.WeightedAGM.Extract
