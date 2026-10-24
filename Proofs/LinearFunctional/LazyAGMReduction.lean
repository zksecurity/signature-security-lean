import Proofs.LinearFunctional.Spec.LazyAGMReduction
import Proofs.BLS.LazyAGMExtraction

/-! Fixed-table semantics and finite-sum extraction identities for the weighted
lazy solvers. Tables and finite-domain sums occur only in these proof bridges. -/

open OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (table_random table_lookup evalTerms_table traceValue
  traceValue_eq_mapIdx traceValue_fst traceValue_snd baseCoeff_traceValue)

namespace Model.LazyAGM.WeightedReduction

variable {F ι M R G₁ G₂ : Type}

def termsValue [AddCommMonoid R] [SMul F R]
    (terms : M → List (ι × F)) (table : ι → R) (m : M) : R :=
  ((terms m).map fun p => p.2 • table p.1).sum

theorem privateRun_table [AddCommMonoid R] [SMul F R]
    (terms : M → List (ι × F)) (table : ι → R) (hash sign : R → G₁)
    (A : Adversary F ι M G₁ G₂) (pk : G₂) :
    simulateQ (BLS.CoCDH.coinTableImpl table) (privateRun terms hash sign A pk) =
      fixedRun A pk (hash ∘ table) (sign ∘ termsValue terms table) := by
  apply simulateQ_StateT_compose (privateOracle terms hash sign) (BLS.CoCDH.coinTableImpl table)
    (fixedImpl (hash ∘ table) (sign ∘ termsValue terms table)) _ (A.main pk) ([], [])
  intro q tr
  rcases q with ((n | i) | m) <;>
    simp [privateOracle, fixedImpl, handler, table_random, table_lookup, evalTerms_table,
      termsValue]

variable [Field F]

theorem signedTerms_value [AddCommGroup R] [Module F R]
    (terms : M → List (ι × F)) (coeff : List F) (tr : List (M × G₁)) (table : ι → R) :
    ((signedTerms terms coeff tr).map fun p => p.2 • table p.1).sum =
      traceValue coeff tr (termsValue terms table) := by
  simp [signedTerms, traceValue_eq_mapIdx, termsValue, List.mapIdx_eq_ofFn,
    List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def,
    List.map_ofFn, List.smul_sum, mul_smul]

theorem termsValue_fst (terms : M → List (ι × F)) (table : ι → F × F) (m : M) :
    (termsValue terms table m).1 = termsValue terms (fun i => (table i).1) m := by
  unfold termsValue
  induction terms m with
  | nil => rfl
  | cons p rest ih => simpa using congrArg (fun r => p.2 * (table p.1).1 + r) ih

theorem termsValue_snd (terms : M → List (ι × F)) (table : ι → F × F) (m : M) :
    (termsValue terms table m).2 = termsValue terms (fun i => (table i).2) m := by
  unfold termsValue
  induction terms m with
  | nil => rfl
  | cons p rest ih => simpa using congrArg (fun r => p.2 * (table p.1).2 + r) ih

/-- General weighted denominator identity. The runtime side uses only the final
message and actual signing replies, even when the proof-side index domain is large. -/
theorem denominatorCoeff_value [Fintype ι] [DecidableEq ι]
    (terms : M → List (ι × F)) (w : ι → M → F)
    (ht : ∀ (table : ι → F) m, termsValue terms table m = ∑ i, table i * w i m)
    (out : Output F M) (tr : Transcript ι M G₁) (table : ι → F) :
    (∑ i, denominatorCoeff w out tr i * table i) =
      termsValue terms table out.mstar - traceValue out.ξ tr.2 (termsValue terms table) := by
  simp only [denominatorCoeff, sub_mul, Finset.sum_sub_distrib, ht]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · rw [traceValue_eq_mapIdx]
    simp only [List.mapIdx_eq_ofFn, List.sum_ofFn, Finset.sum_mul, smul_eq_mul, ht,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro i _
    ring

variable [AddCommGroup G₁] [Module F G₁]

theorem goodProgram_table (terms : M → List (ι × F)) (rho : ι → F)
    (g X : G₁) (pk : G₂) (A : Adversary F ι M G₁ G₂) :
    simulateQ (BLS.CoCDH.coinTableImpl rho) (goodProgram terms g X pk A) = (do
      let (out, tr) ← fixedRun A pk (fun i => rho i • g)
        (fun m => termsValue terms rho m • X)
      pure ((out.β + traceValue out.γ tr.1 rho) /
        (termsValue terms rho out.mstar - traceValue out.ξ tr.2 (termsValue terms rho)))) := by
  simp only [goodProgram, simulateQ_bind, privateRun_table, evalTerms_table, simulateQ_pure,
    pure_bind, signedTerms_value]
  rfl

theorem badProgram_table (terms : M → List (ι × F)) (masks : ι → F × F)
    (g X : G₁) (pk : G₂) (kappa : F) (A : Adversary F ι M G₁ G₂) :
    simulateQ (BLS.CoCDH.coinTableImpl masks) (badProgram terms g X pk kappa A) = (do
      let (out, tr) ← fixedRun A pk
        (fun i => (masks i).1 • X + (masks i).2 • g)
        (fun m => kappa • ((termsValue terms masks m).1 • X +
          (termsValue terms masks m).2 • g))
      let signed := traceValue out.ξ tr.2 (termsValue terms masks)
      let target := termsValue terms masks out.mstar
      pure (-(target.2 - signed.2) / (target.1 - signed.1))) := by
  simp [badProgram, privateRun_table, evalTerms_table, signedTerms_value,
    termsValue, Function.comp_def]

end Model.LazyAGM.WeightedReduction
