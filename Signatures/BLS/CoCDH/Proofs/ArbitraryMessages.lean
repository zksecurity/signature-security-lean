import Signatures.BLS.CoCDH.Proofs.QueryBound
import Signatures.BLS.CoCDH.Proofs.FinitePublicKeys
import Signatures.BLS.CoCDH.Proofs.CoronMessageTransport

/-! The original Coron success inequality for arbitrary message types. A finite
cover of the attacker's adaptive tree is used only inside the proof; exact game
and solver transport returns the original lazy computations. Neither the
attacker nor the executed reduction enumerates this cover. -/

open BLS.ROM

open OracleComp OracleSpec BilinearGroup BLS.CoCDH.Tight

namespace BLS.CoCDH.Proofs

variable {F M G₁ G₂ Gₜ : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [SampleableType G₁] [Fintype G₁] [DecidableEq G₁]
  [AddCommGroup G₂] [Module F G₂] [AddCommGroup Gₜ] [Module F Gₜ]
  [BilinearPairing F G₁ G₂ Gₜ] [DecidableEq Gₜ]

theorem security_arbitrary_messages (g : G₁) (g₂ : G₂) (qS : Nat) (adv : AdversaryPK M G₁ G₂)
    (hgen : Function.Bijective (fun r : F => r • g))
    (hinj : Function.Injective (fun z : G₁ => pairing (F := F) (Gₜ := Gₜ) z g₂))
    (hqs : ∀ r : F, IsQueryBoundP (adv (r • g₂)) (fun i => Sum.isRight i = true) qS) :
    𝒟[blsEufLazyPK (F := F) (Gₜ := Gₜ) g g₂ adv] {true} ≤
      Model.coronFactor qS * Model.coCDHAdvantage g g₂
        (coronReductionLazyPK (F := F) qS (cacheForgeryPK adv)) := by
  classical
  obtain ⟨cover, restricted, heq⟩ := exists_restricted_publicKeys (fun r : F => r • g₂) adv
  let mapped : AdversaryPK M G₁ G₂ := fun pk => mapMessages Subtype.val (restricted pk)
  have hkey : ∀ r : F, adv (r • g₂) = mapped (r • g₂) := fun r => (heq r).symm
  have hsource := (blsEufLazyPK_congr_generated (Gₜ := Gₜ) g g₂ adv mapped hkey).trans
    (blsEufLazyPK_mapMessages (Gₜ := Gₜ) Subtype.val Subtype.val_injective g g₂ restricted)
  have htarget := (MessageTransport.coCDHExp_coron_congr_generated g g₂ qS adv mapped hkey).trans
    (MessageTransport.coCDHExp_coron_mapMessages Subtype.val Subtype.val_injective g g₂ qS restricted)
  have hqs' : ∀ r : F, IsQueryBoundP (restricted (r • g₂)) (fun i => Sum.isRight i = true) qS := by
    intro r
    apply (mapMessages_signing_bound Subtype.val (restricted (r • g₂)) qS).mp
    rw [heq r]
    exact hqs r
  rw [hsource, Model.coCDHAdvantage, htarget]
  exact security g g₂ qS restricted hgen hinj hqs'

end BLS.CoCDH.Proofs
