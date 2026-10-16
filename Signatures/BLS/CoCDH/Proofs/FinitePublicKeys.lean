import Signatures.BLS.CoCDH.Proofs.MessageTransport

/-! A finite proof domain is needed only at generated public keys. Other inputs
can be filled by a covered default computation in this proof-only presentation;
the executable attacker and reduction are not changed. -/

open BLS.ROM

open OracleComp OracleSpec

namespace BLS.CoCDH.Tight

variable {N M G₁ G₂ K : Type}

noncomputable def restrictPublicKeys (cover : Finset M) (adv : AdversaryPK M G₁ G₂)
    (defaultKey : G₂) (hdefault : MessageCovered cover (adv defaultKey)) :
    AdversaryPK {m // m ∈ cover} G₁ G₂ := by
  classical
  exact fun pk => if h : MessageCovered cover (adv pk) then restrictMessages cover (adv pk) h
    else restrictMessages cover (adv defaultKey) hdefault

theorem map_restrictPublicKeys (cover : Finset M) (adv : AdversaryPK M G₁ G₂)
    (defaultKey : G₂) (hdefault : MessageCovered cover (adv defaultKey))
    (pk : G₂) (hpk : MessageCovered cover (adv pk)) :
    mapMessages Subtype.val (restrictPublicKeys cover adv defaultKey hdefault pk) = adv pk := by
  simp only [restrictPublicKeys, dite_eq_left hpk, mapMessages_restrictMessages]

/-- The public-key type need not be finite. Only the generating seed type is
finite; the common finite cover works for every seed and every adaptive reply. -/
theorem exists_restricted_publicKeys [Finite K] [Nonempty K] [Finite G₁]
    (key : K → G₂) (adv : AdversaryPK M G₁ G₂) :
    ∃ cover : Finset M, ∃ restricted : AdversaryPK {m // m ∈ cover} G₁ G₂,
      ∀ seed, mapMessages Subtype.val (restricted (key seed)) = adv (key seed) := by
  classical
  obtain ⟨cover, hcover⟩ := exists_message_cover (fun seed => adv (key seed))
  let seed : K := Classical.choice inferInstance
  exact ⟨cover, restrictPublicKeys cover adv (key seed) (hcover seed),
    fun k => map_restrictPublicKeys cover adv (key seed) (hcover seed) (key k) (hcover k)⟩

open BilinearGroup

variable {F Gₜ : Type} [Field F] [SampleableType F] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [AddCommGroup Gₜ] [Module F Gₜ] [BilinearPairing F G₁ G₂ Gₜ]

theorem blsEufLazyPK_congr_generated (g : G₁) (g₂ : G₂) (adv adv' : AdversaryPK M G₁ G₂)
    (h : ∀ r : F, adv (r • g₂) = adv' (r • g₂)) :
    blsEufLazyPK (F := F) (Gₜ := Gₜ) g g₂ adv = blsEufLazyPK (F := F) (Gₜ := Gₜ) g g₂ adv' := by
  unfold blsEufLazyPK blsEufTightPK cacheForgeryPK
  exact bind_congr fun r => by rw [h r]

end BLS.CoCDH.Tight
