import Signatures.OOPS.Proofs.LazyAGM
import Signatures.LinearFunctional.Proofs.LazyAGMCoupling

/-! The established OOPS probability bound with lazy weighted solvers.
Finite topics are used in this comparison proof only. Removing that proof-side
restriction and deriving native execution budgets are separate obligations. -/

open OracleComp AlgebraicGroupModel Model.LazyAGM

namespace OOPS.LazyAGM.Proofs

variable {F T G₁ G₂ Gₜ : Type}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [Fintype T] [DecidableEq T]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem termsValue_eq (d : Nat) (table : T × Fin (d + 1) → F) (m : F × T) :
    WeightedReduction.termsValue (terms d) table m = ∑ i, table i * OOPS.Handle.oopsWMulti d i m := by
  unfold WeightedReduction.termsValue
  rw [terms_eq]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The source game retains its original distinct-message condition on the
target topic. Both solvers use a finite list cache of encountered base indices. -/
theorem security_lazy_finite_topics (g₁ : G₁) (g₂ : G₂) (d : Nat)
    (A : Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂)
    (hgen : Function.Bijective (fun rho : F => rho • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d A] {true} ≤
      Model.dlog11Advantage g₁ g₂ (WeightedReduction.goodReductionList (terms d) A) +
      Model.dlog11Advantage g₁ g₂ (WeightedReduction.badReductionList (terms d) A) +
      1 / (Fintype.card F : ENNReal) := by
  rw [WeightedReduction.goodAdvantage_eq_eager (terms d) (OOPS.Handle.oopsWMulti d) (termsValue_eq d),
    WeightedReduction.badAdvantage_eq_eager (terms d) (OOPS.Handle.oopsWMulti d) (termsValue_eq d)]
  exact security g₁ g₂ d A hgen hpair

end OOPS.LazyAGM.Proofs
