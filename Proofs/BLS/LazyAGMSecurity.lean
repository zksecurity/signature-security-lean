import Proofs.BLS.LazyAGM
import Proofs.BLS.LazyAGMCoupling

/-! The established finite-message BLS AGM probability bound, now using the
two lazy, transcript-extracting solvers. This probability theorem does not assert
their runtime bounds. `LazyAGMArbitraryMessages` uses this finite-domain helper
to prove the bound for arbitrary message types. -/

open BilinearGroup

open OracleComp AlgebraicGroupModel Model.LazyAGM MeasureTheory

namespace BLS.LazyAGM.Reduction

variable {F M G₁ G₂ Gₜ : Type}
  [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

local instance : MeasurableSpace F := ⊤

theorem dlog11Advantage_congr (g₁ : G₁) (g₂ : G₂)
    (B C : DLog11Adversary F G₁ G₂)
    (h : ∀ x : F, 𝒟[B g₁ (x • g₁) g₂ (x • g₂)] =
      𝒟[C g₁ (x • g₁) g₂ (x • g₂)]) :
    Model.dlog11Advantage g₁ g₂ B = Model.dlog11Advantage g₁ g₂ C := by
  unfold Model.dlog11Advantage
  apply congrArg (fun μ : Measure Bool => μ {true})
  unfold dlog11Exp
  apply evalDist_bind_congr
  intro x
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, h x]

variable [Fintype M] [DecidableEq M]

theorem goodAdvantage_eq_eager (g₁ : G₁) (g₂ : G₂) (A : Adversary F M M G₁ G₂) :
    Model.dlog11Advantage g₁ g₂ (goodReductionLazy A) =
      Model.dlog11Advantage g₁ g₂ (goodReduction BLS.Proofs.indicatorWeight A) := by
  apply dlog11Advantage_congr
  intro x
  exact goodReductionLazy_eq_eager A g₁ (x • g₁) g₂ (x • g₂)

theorem badAdvantage_eq_eager (g₁ : G₁) (g₂ : G₂) (A : Adversary F M M G₁ G₂) :
    Model.dlog11Advantage g₁ g₂ (badReductionLazy A) =
      Model.dlog11Advantage g₁ g₂ (badReduction BLS.Proofs.indicatorWeight A) := by
  apply dlog11Advantage_congr
  intro x
  exact badReductionLazy_eq_eager A g₁ (x • g₁) g₂ (x • g₂)

variable [Fintype F] [DecidableEq F] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

/-- Same success loss as the established AGM theorem, for the new lazy solvers.
No claim about a concrete runtime or unrestricted PPT attackers is made here. -/
theorem security_finite_messages (g₁ : G₁) (g₂ : G₂) (A : Adversary F M M G₁ G₂)
    (hgen : Function.Bijective (fun rho : F => rho • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[BLS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A] {true} ≤
      Model.dlog11Advantage g₁ g₂ (goodReductionLazy A) +
      Model.dlog11Advantage g₁ g₂ (badReductionLazy A) +
      1 / (Fintype.card F : ENNReal) := by
  rw [goodAdvantage_eq_eager, badAdvantage_eq_eager]
  exact BLS.LazyAGM.Proofs.security g₁ g₂ A hgen hpair

end BLS.LazyAGM.Reduction
