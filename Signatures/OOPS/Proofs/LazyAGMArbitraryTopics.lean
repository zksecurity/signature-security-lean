import Signatures.OOPS.Proofs.LazyAGMSecurity
import Signatures.OOPS.Proofs.LazyAGMTopicTransport

/-! OOPS's original lazy AGM probability bound for arbitrary topic types.
The finite topic presentation is used only in the proof and is never enumerated
by either weighted list-cache reduction. -/

open BilinearGroup

open OracleComp AlgebraicGroupModel Model.LazyAGM
open Model.LazyAGM.WeightedReduction Model.LazyAGM.WeightedTransport
open OOPS.LazyAGM.TopicTransport

namespace OOPS.LazyAGM.Proofs

variable {F T G₁ G₂ Gₜ : Type}
  [Field F] [SampleableType F] [Fintype F] [DecidableEq F] [DecidableEq T]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem security_arbitrary_topics (g₁ : G₁) (g₂ : G₂) (d : Nat)
    (A : Adversary F (T × Fin (d + 1)) (F × T) G₁ G₂)
    (hgen : Function.Bijective (fun rho : F => rho • g₁))
    (hpair : Function.Injective (fun c : F => c • (pairing (F := F) g₁ g₂ : Gₜ))) :
    𝒟[OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d A] {true} ≤
      Model.dlog11Advantage g₁ g₂ (goodReductionList (terms d) A) +
      Model.dlog11Advantage g₁ g₂ (badReductionList (terms d) A) +
      1 / (Fintype.card F : ENNReal) := by
  classical
  obtain ⟨cover, restricted, heq⟩ := exists_restricted_publicKeys g₂ d A
  let mapped := mapAdversary (index Subtype.val) (message Subtype.val) restricted
  have hkey : ∀ r : F, A.main (r • g₂) = mapped.main (r • g₂) := fun r => (heq r).symm
  have hsource : OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d A =
      OOPS.LazyAGM.game (Gₜ := Gₜ) g₁ g₂ d restricted := by
    rw [game_eq_of_decidableEq, game_eq_of_decidableEq]
    exact (game_congr_generated (terms d) (admissible d) g₁ g₂ A mapped hkey).trans
      (WeightedTransport.game_map (index Subtype.val) (index_injective _ Subtype.val_injective)
        (message Subtype.val) (message_injective _ Subtype.val_injective) (terms d) (terms d)
        (terms_map Subtype.val) (admissible d) (admissible d)
        (admissible_map _ Subtype.val_injective) g₁ g₂ restricted)
  have hgood := goodExp_congr_generated (terms d) g₁ g₂ A mapped hkey
  have hbad := badExp_congr_generated (terms d) g₁ g₂ A mapped hkey
  dsimp only [mapped] at hgood hbad
  rw [goodReduction_map (index Subtype.val) (index_injective _ Subtype.val_injective)
    (message Subtype.val) (terms d) (terms d) (terms_map Subtype.val)] at hgood
  rw [badReduction_map (index Subtype.val) (index_injective _ Subtype.val_injective)
    (message Subtype.val) (terms d) (terms d) (terms_map Subtype.val)] at hbad
  rw [hsource, Model.dlog11Advantage, Model.dlog11Advantage, hgood, hbad]
  exact security_lazy_finite_topics g₁ g₂ d restricted hgen hpair

end OOPS.LazyAGM.Proofs
