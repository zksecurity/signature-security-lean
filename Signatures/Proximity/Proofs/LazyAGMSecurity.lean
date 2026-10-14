import Signatures.Proximity.Proofs.LazyAGM
import Signatures.LinearFunctional.Proofs.LazyAGMCoupling

/-! Proximity's probability bound with lazy weighted solvers and the original
fresh-collision probability. Finite slots remain a proof-side restriction here;
the solver programs and caches do not enumerate the slot domain. -/

open OracleComp AlgebraicGroupModel Model.LazyAGM

namespace Proximity.LazyAGM.Proofs

variable {F S G₁ G₂ Gₜ : Type} {ℓ : Nat}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [Fintype S] [DecidableEq S]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem termsValue_eq (table : Option (Fin ℓ) × S → F) (m : (Fin ℓ → F) × S) :
    WeightedReduction.termsValue terms table m =
      ∑ i, table i * Proximity.Proofs.coordinateWeight ℓ i m := by
  unfold WeightedReduction.termsValue
  rw [terms_eq]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The actual source collision experiment remains in the bound. Neither the
game nor the lazy reductions acquire an assumed noncollision restriction. -/
theorem security_lazy_finite_slots (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂)
    (hgen : Function.Bijective (fun rho : F => rho • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[Proximity.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A] {true} ≤
      Model.dlog11Advantage g₁ g₂ (WeightedReduction.goodReductionList terms A) +
      Model.dlog11Advantage g₁ g₂ (WeightedReduction.badReductionList terms A) +
      1 / (Fintype.card F : ENNReal) + 𝒟[collisionGame g₂ A] {true} := by
  rw [WeightedReduction.goodAdvantage_eq_eager terms (Proximity.Proofs.coordinateWeight ℓ) termsValue_eq,
    WeightedReduction.badAdvantage_eq_eager terms (Proximity.Proofs.coordinateWeight ℓ) termsValue_eq]
  exact security g₁ g₂ A hgen hpair

end Proximity.LazyAGM.Proofs
