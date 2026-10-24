import Signatures.OOPS.Spec.LazyAGM
import Proofs.OOPS.Adaptive
import Proofs.LinearFunctional.LazyAGM

open BilinearGroup

open OracleComp AlgebraicGroupModel AlgebraicGroupModel.LinFunctional
open Model.LazyAGM Model.LazyAGM.Proofs OOPS.Handle

namespace OOPS.LazyAGM.Proofs

variable {F T G₁ G₂ Gₜ : Type}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [Fintype T] [DecidableEq T]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem terms_eq (d : Nat) (H : T × Fin (d + 1) → G₁) (mt : F × T) :
    (List.map (fun p => p.2 • H p.1) (terms d mt)).sum =
      ∑ i, oopsWMulti d i mt • H i := by
  rw [terms, List.map_ofFn, List.sum_ofFn]
  simp [oopsWMulti, Fintype.sum_prod_type]

theorem admissible_eq (d : Nat) (fo : DynForgery F (F × T) (T × Fin (d + 1))) :
    admissibleForgery (admissible d) fo ↔ (targetMessages fo.2.v fo.2.mstar.2).card ≤ d := by
  simp only [admissibleForgery, admissible, ← targetMessages_eq_ofFn]

theorem security (g₁ : G₁) (g₂ : G₂) (d : Nat)
    (A : Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂)
    (hgen : Function.Bijective (fun ρ : F => ρ • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d A] {true} ≤
      Model.dlog11Advantage g₁ g₂ (goodReduction (oopsWMulti d) A) +
      Model.dlog11Advantage g₁ g₂ (badReduction (oopsWMulti d) A) +
      1 / (Fintype.card F : ENNReal) := by
  rw [game_eq_of_decidableEq]
  change advantage (Gₜ := Gₜ) (terms d) (admissible d) g₁ g₂ A ≤ _
  rw [advantage_eq_realGame (terms d) (oopsWMulti d) (terms_eq d),
    goodAdvantage_eq, badAdvantage_eq]
  simp only [admissible_eq]
  exact OOPS.Proofs.adaptive_security g₁ g₂ d (extracted A) hgen hpair

end OOPS.LazyAGM.Proofs
