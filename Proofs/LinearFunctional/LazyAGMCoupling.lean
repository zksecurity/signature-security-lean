import Proofs.LinearFunctional.LazyAGMReduction
import Proofs.BLS.LazyAGMSecurity
import Proofs.BLS.LazyAGMList

/-! Joint deferred sampling for weighted lazy AGM solvers. The entire adaptive
interaction, weighted transcript extraction, and final target use the same
cache. Finite tables appear only in the comparison with the existing proof. -/

open OracleComp OracleSpec Model.LazyAGM
open BLS.LazyAGM.Reduction (lazyRun_eq_table maskTable_bind baseCoeff_traceValue
  traceValue_eq_mapIdx traceValue_fst traceValue_snd privateListRun_erase dlog11Advantage_congr)

namespace Model.LazyAGM.WeightedReduction

variable {F ι M G₁ G₂ : Type}
  [Field F] [SampleableType F] [DecidableEq ι]
  [AddCommGroup G₁] [Module F G₁]

theorem goodReductionList_eq (terms : M → List (ι × F)) (A : Adversary F ι M G₁ G₂) :
    goodReductionList terms A = goodReductionLazy terms A := by
  funext g X g₂ pk
  unfold goodReductionList goodReductionLazy
  rw [privateListRun_erase, QueryImpl.ListCache.decode_nil]

section FiniteIndex

variable [Fintype ι] [MeasurableSpace F]

theorem goodReductionLazy_eq_eager (terms : M → List (ι × F)) (w : ι → M → F)
    (ht : ∀ (table : ι → F) m, termsValue terms table m = ∑ i, table i * w i m)
    (A : Adversary F ι M G₁ G₂) (g X : G₁) (g₂ pk : G₂) :
    𝒟[goodReductionLazy terms A g X g₂ pk] = 𝒟[goodReduction w A g X g₂ pk] := by
  rw [goodReductionLazy, lazyRun_eq_table]
  apply congrArg evalDist
  unfold goodReduction
  apply bind_congr
  intro rho
  rw [goodProgram_table]
  simp only [ht, baseCoeff_traceValue, traceValue_eq_mapIdx, smul_eq_mul]

end FiniteIndex

variable [AddCommGroup G₂] [Module F G₂]

theorem badReductionList_eq (terms : M → List (ι × F)) (A : Adversary F ι M G₁ G₂) :
    badReductionList terms A = badReductionLazy terms A := by
  funext g X g₂ pk
  unfold badReductionList badReductionLazy
  apply bind_congr
  intro kappa
  rw [privateListRun_erase, QueryImpl.ListCache.decode_nil]

section FiniteIndex

variable [Fintype ι] [MeasurableSpace F]

theorem badReductionLazy_eq_eager (terms : M → List (ι × F)) (w : ι → M → F)
    (ht : ∀ (table : ι → F) m, termsValue terms table m = ∑ i, table i * w i m)
    (A : Adversary F ι M G₁ G₂) (g X : G₁) (g₂ pk : G₂) :
    𝒟[badReductionLazy terms A g X g₂ pk] = 𝒟[badReduction w A g X g₂ pk] := by
  unfold badReductionLazy badReduction
  apply evalDist_bind_congr
  intro kappa
  rw [lazyRun_eq_table, maskTable_bind]
  apply congrArg evalDist
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  rw [badProgram_table]
  simp only [denominatorCoeff_value terms w ht, traceValue_fst, traceValue_snd,
    termsValue_fst, termsValue_snd]
  have hsign : (fun m => kappa • (termsValue terms a m • X + termsValue terms b m • g)) =
      (fun m => kappa • ∑ i, w i m • (a i • X + b i • g)) := by
    funext m
    simp [ht, Finset.sum_smul, smul_add, Finset.sum_add_distrib, mul_smul, mul_comm]
  rw [hsign]

end FiniteIndex

section Advantage

variable [Fintype ι]
local instance : MeasurableSpace F := ⊤

theorem goodAdvantage_eq_eager (terms : M → List (ι × F)) (w : ι → M → F)
    (ht : ∀ (table : ι → F) m, termsValue terms table m = ∑ i, table i * w i m)
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F ι M G₁ G₂) :
    Model.dlog11Advantage g₁ g₂ (goodReductionList terms A) =
      Model.dlog11Advantage g₁ g₂ (goodReduction w A) := by
  rw [goodReductionList_eq]
  apply dlog11Advantage_congr
  intro x
  exact goodReductionLazy_eq_eager terms w ht A g₁ (x • g₁) g₂ (x • g₂)

theorem badAdvantage_eq_eager (terms : M → List (ι × F)) (w : ι → M → F)
    (ht : ∀ (table : ι → F) m, termsValue terms table m = ∑ i, table i * w i m)
    (g₁ : G₁) (g₂ : G₂) (A : Adversary F ι M G₁ G₂) :
    Model.dlog11Advantage g₁ g₂ (badReductionList terms A) =
      Model.dlog11Advantage g₁ g₂ (badReduction w A) := by
  rw [badReductionList_eq]
  apply dlog11Advantage_congr
  intro x
  exact badReductionLazy_eq_eager terms w ht A g₁ (x • g₁) g₂ (x • g₂)

end Advantage

end Model.LazyAGM.WeightedReduction
