import Proofs.LinearFunctional.LazyAGMCacheBound

/-! Sharp entry counts for the actual BLS list-cache reductions. The weighted
singleton specialization preserves the entire query computation, so its cache
invariant applies before any output/cache projection. Private random requests
and extraction rereads add no entries; only hashing, signing, and the final
target can do so. These entry counts complement the existing runtime bounds. -/

open OracleComp OracleSpec Model.LazyAGM
open Model.LazyAGM.WeightedReduction (hashQuery signingQuery)

namespace BLS.LazyAGM.Reduction

variable {F M R G₁ G₂ : Type} [Field F]

private theorem evalTerms_singleton [AddCommMonoid R] [Module F R] (m : M) :
    (evalTerms (BLS.LazyAGM.terms (F := F) m) : OracleComp (baseSpec M R) R) =
      liftM ((baseSpec M R).query (.inr m)) := by
  simp [BLS.LazyAGM.terms, evalTerms]

private theorem privateOracle_singleton [AddCommMonoid R] [Module F R]
    (hash sign : R → G₁) :
    WeightedReduction.privateOracle (BLS.LazyAGM.terms (F := F) (M := M)) hash sign =
      privateOracle hash sign := by
  funext q tr
  rcases q with ((n | m) | m) <;>
    simp [WeightedReduction.privateOracle, privateOracle, handler, evalTerms_singleton]

private theorem privateRun_singleton [AddCommMonoid R] [Module F R]
    (hash sign : R → G₁) (A : Adversary F M M G₁ G₂) (pk : G₂) :
    WeightedReduction.privateRun BLS.LazyAGM.terms hash sign A pk =
      privateRun hash sign A pk := by
  simp only [WeightedReduction.privateRun, privateRun, privateOracle_singleton]

private theorem signedTerms_singleton (coeff : List F) (tr : List (M × G₁)) :
    WeightedReduction.signedTerms BLS.LazyAGM.terms coeff tr = traceTerms coeff tr := by
  simp only [WeightedReduction.signedTerms, BLS.LazyAGM.terms, traceTerms,
    List.map_singleton, mul_one, List.mapIdx_eq_ofFn]
  simpa only [List.flatMap, List.map_ofFn, Function.comp_def] using
    List.flatMap_singleton' (List.ofFn fun i : Fin tr.length => ((tr.get i).1, tokenCoeff coeff i.val))

variable [AddCommGroup G₁] [Module F G₁]

/-- Singleton weighted terms give exactly the BLS good-branch computation. -/
theorem weighted_goodProgram_eq (g X : G₁) (pk : G₂) (A : Adversary F M M G₁ G₂) :
    WeightedReduction.goodProgram BLS.LazyAGM.terms g X pk A = goodProgram g X pk A := by
  simp only [WeightedReduction.goodProgram, goodProgram, privateRun_singleton,
    signedTerms_singleton, evalTerms_singleton]

/-- The same equality preserves the independent mask-pair branch. -/
theorem weighted_badProgram_eq (g X : G₁) (pk : G₂) (kappa : F)
    (A : Adversary F M M G₁ G₂) :
    WeightedReduction.badProgram BLS.LazyAGM.terms g X pk kappa A =
      badProgram g X pk kappa A := by
  simp only [WeightedReduction.badProgram, badProgram, privateRun_singleton,
    signedTerms_singleton, evalTerms_singleton]

variable [SampleableType F] [DecidableEq M]

/-- At most one entry per hash/sign call and one for the frozen final target. -/
theorem goodList_cache_bound_by_kind (g X : G₁) (pk : G₂)
    (A : Adversary F M M G₁ G₂) (hashes signatures : Nat)
    (hh : IsQueryBoundP (A.main pk) (fun q => hashQuery q = true) hashes)
    (hs : IsQueryBoundP (A.main pk) (fun q => signingQuery q = true) signatures)
    (z : F × List (M × F))
    (hz : z ∈ support ((simulateQ privateListOracle (goodProgram g X pk A)).run [])) :
    z.2.length ≤ hashes + signatures + 1 := by
  have h := WeightedReduction.goodProgram_cache_bound BLS.LazyAGM.terms 1
    (by intro m; simp [BLS.LazyAGM.terms]) g X pk A hashes signatures hh hs z
    (by simpa only [weighted_goodProgram_eq] using hz)
  simpa only [Nat.mul_one, Nat.add_assoc] using h

/-- The masked branch has the same count, for every chosen signing key. -/
theorem badList_cache_bound_by_kind (g X : G₁) (pk : G₂) (kappa : F)
    (A : Adversary F M M G₁ G₂) (hashes signatures : Nat)
    (hh : IsQueryBoundP (A.main pk) (fun q => hashQuery q = true) hashes)
    (hs : IsQueryBoundP (A.main pk) (fun q => signingQuery q = true) signatures)
    (z : F × List (M × (F × F)))
    (hz : z ∈ support ((simulateQ privateListOracle (badProgram g X pk kappa A)).run [])) :
    z.2.length ≤ hashes + signatures + 1 := by
  have h := WeightedReduction.badProgram_cache_bound BLS.LazyAGM.terms 1
    (by intro m; simp [BLS.LazyAGM.terms]) g X pk kappa A hashes signatures hh hs z
    (by simpa only [weighted_badProgram_eq] using hz)
  simpa only [Nat.mul_one, Nat.add_assoc] using h

end BLS.LazyAGM.Reduction
