import Proofs.LinearFunctional.LazyAGMCache

/-! A cache bound for the complete weighted reductions. Extraction revisits
previously cached bases. Only explicit hash calls, signing calls, and the final
target can add entries: at most `qH + (qS + 1) * L` in either branch. This is
an entry-count theorem, not a replacement for the complete runtime certificate. -/

open OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle traceTerms)

namespace Model.LazyAGM.WeightedReduction

variable {F ι M G₁ G₂ : Type} [Field F] [SampleableType F] [DecidableEq ι]
  [AddCommGroup G₁] [Module F G₁]

theorem goodProgram_cache_bound (terms : M → List (ι × F))
    (length : Nat) (hl : ∀ m, (terms m).length ≤ length)
    (g X : G₁) (pk : G₂) (A : Adversary F ι M G₁ G₂) (hashes signatures : Nat)
    (hh : IsQueryBoundP (A.main pk) (fun q => hashQuery q = true) hashes)
    (hs : IsQueryBoundP (A.main pk) (fun q => signingQuery q = true) signatures)
    (z : F × List (ι × F))
    (hz : z ∈ support ((simulateQ privateListOracle (goodProgram terms g X pk A)).run [])) :
    z.2.length ≤ hashes + (signatures + 1) * length := by
  simp only [goodProgram, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨started, hstarted, hashed, hhashed, signed, hsigned, target, htarget, rfl⟩ := hz
  obtain ⟨hc, hlen⟩ := privateRun_cache terms (fun rho : F => rho • g) (fun rho => rho • X)
    length hl A pk hashes signatures hh hs started hstarted
  have hhash := evalTerms_cached (traceTerms started.1.1.γ started.1.2.1) started.2
    (hashTerms_cached _ _ _ hc.1) hashed hhashed
  have hsign := evalTerms_cached (signedTerms terms started.1.1.ξ started.1.2.2) started.2
    (signedTerms_cached _ _ _ _ hc.2) signed (by simpa only [hhash] using hsigned)
  have htargetlen := (evalTerms_list_preserves (terms started.1.1.mstar) signed.2 target htarget).2.2
  rw [hsign] at htargetlen
  have hl := hl started.1.1.mstar
  dsimp only
  nlinarith

theorem badProgram_cache_bound (terms : M → List (ι × F))
    (length : Nat) (hl : ∀ m, (terms m).length ≤ length)
    (g X : G₁) (pk : G₂) (kappa : F) (A : Adversary F ι M G₁ G₂) (hashes signatures : Nat)
    (hh : IsQueryBoundP (A.main pk) (fun q => hashQuery q = true) hashes)
    (hs : IsQueryBoundP (A.main pk) (fun q => signingQuery q = true) signatures)
    (z : F × List (ι × (F × F)))
    (hz : z ∈ support ((simulateQ privateListOracle (badProgram terms g X pk kappa A)).run [])) :
    z.2.length ≤ hashes + (signatures + 1) * length := by
  simp only [badProgram, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at hz
  obtain ⟨started, hstarted, signed, hsigned, target, htarget, rfl⟩ := hz
  obtain ⟨hc, hlen⟩ := privateRun_cache terms (fun masks : F × F => masks.1 • X + masks.2 • g)
    (fun masks => kappa • (masks.1 • X + masks.2 • g))
    length hl A pk hashes signatures hh hs started hstarted
  have hsign := evalTerms_cached (signedTerms terms started.1.1.ξ started.1.2.2) started.2
    (signedTerms_cached _ _ _ _ hc.2) signed hsigned
  have htargetlen := (evalTerms_list_preserves (terms started.1.1.mstar) signed.2 target htarget).2.2
  rw [hsign] at htargetlen
  have hl := hl started.1.1.mstar
  dsimp only
  nlinarith

end Model.LazyAGM.WeightedReduction
