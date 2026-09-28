import Signatures.BLS.Spec.LazyAGM
import Signatures.BLS.Proofs.Nondegeneracy
import Signatures.LinearFunctional.Proofs.LazyAGM

open OracleComp AlgebraicGroupModel AlgebraicGroupModel.LinFunctional
open Model.LazyAGM Model.LazyAGM.Proofs

namespace BLS.LazyAGM.Proofs

variable {F M G₁ G₂ Gₜ : Type}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [Fintype M] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem security (g₁ : G₁) (g₂ : G₂) (A : Adversary F M M G₁ G₂)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[BLS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A] {true} ≤
      Model.dlog11Advantage g₁ g₂ (goodReduction BLS.Proofs.indicatorWeight A) +
      Model.dlog11Advantage g₁ g₂ (badReduction BLS.Proofs.indicatorWeight A) +
      1 / (Fintype.card F : ENNReal) := by
  apply Model.LazyAGM.Proofs.security terms BLS.Proofs.indicatorWeight
    (fun H m => by simp [terms, BLS.Proofs.indicatorWeight]) (fun _ _ => True)
    g₁ g₂ A (fun fo => fo.2.mstar) hgen
    (fun fo _ hfresh => BLS.Proofs.fresh_coefficient fo hfresh) hpair

end BLS.LazyAGM.Proofs
