import Signatures.Proximity.Proofs.LazyAGMSecurity
import Signatures.Proximity.Proofs.LazyAGMSlotTransport

/-! Proximity's weighted lazy probability reduction for arbitrary slot types.
The source game and actual fresh-collision term are preserved by the same
finite proof presentation; no slot universe is enumerated at runtime. -/

open BilinearGroup

open OracleComp AlgebraicGroupModel Model.LazyAGM
open Model.LazyAGM.WeightedReduction Model.LazyAGM.WeightedTransport
open Proximity.LazyAGM.SlotTransport

namespace Proximity.LazyAGM.Proofs

variable {F S G₁ G₂ Gₜ : Type} {ℓ : Nat}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq S]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem security_arbitrary_slots (g₁ : G₁) (g₂ : G₂)
    (A : Adversary F (Option (Fin ℓ) × S) ((Fin ℓ → F) × S) G₁ G₂)
    (hgen : Function.Bijective (fun rho : F => rho • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[Proximity.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ A] {true} ≤
      Model.dlog11Advantage g₁ g₂ (goodReductionList terms A) +
      Model.dlog11Advantage g₁ g₂ (badReductionList terms A) +
      1 / (Fintype.card F : ENNReal) + 𝒟[collisionGame g₂ A] {true} := by
  classical
  obtain ⟨cover, restricted, heq⟩ := exists_restricted_publicKeys g₂ A
  let mapped := mapAdversary (index Subtype.val) (message Subtype.val) restricted
  have hkey : ∀ r : F, A.main (r • g₂) = mapped.main (r • g₂) := fun r => (heq r).symm
  have hsource := (game_congr_generated terms (fun _ _ => True) g₁ g₂ A mapped hkey).trans
    (SlotTransport.game_map (Gₜ := Gₜ) Subtype.val Subtype.val_injective g₁ g₂ restricted)
  have hcollision := (collisionGame_congr_generated g₂ A mapped hkey).trans
    (collisionGame_map Subtype.val Subtype.val_injective g₂ restricted)
  have hgood := goodExp_congr_generated terms g₁ g₂ A mapped hkey
  have hbad := badExp_congr_generated terms g₁ g₂ A mapped hkey
  dsimp only [mapped] at hgood hbad
  rw [goodReduction_map (index Subtype.val) (index_injective _ Subtype.val_injective)
    (message Subtype.val) terms terms (terms_map Subtype.val)] at hgood
  rw [badReduction_map (index Subtype.val) (index_injective _ Subtype.val_injective)
    (message Subtype.val) terms terms (terms_map Subtype.val)] at hbad
  change 𝒟[Model.LazyAGM.game (Gₜ := Gₜ) terms (fun _ _ => True) g₁ g₂ A] {true} ≤ _
  rw [hsource, hcollision, Model.dlog11Advantage, Model.dlog11Advantage, hgood, hbad]
  exact security_lazy_finite_slots g₁ g₂ restricted hgen hpair

end Proximity.LazyAGM.Proofs
