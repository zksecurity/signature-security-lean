import Proofs.Schnorr.NonzeroNonce

/-! Native ROM security for nonzero signing nonces. The signing simulation
collision denominator is |F|-1; the fork challenge denominator remains |F|. -/

open OracleComp OracleSpec DiffieHellman OracleComp.DeferredSampling
open scoped ENNReal

namespace Schnorr.NonzeroNonce

variable {F G M : Type} [Field F] [SampleableType F] [SampleableType Fˣ]
  [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G]
  [SampleableType G] [DecidableEq G]

/-- The simulated commitment is uniform on the nonidentity group elements. -/
theorem sim_commit (g : G) (hg : Function.Bijective (fun x : F => x • g)) (pk : G) :
    (Prod.fst <$> simTranscript (F := F) g pk) =ᵈ ((fun a : Fˣ => (a : F) • g) <$> ($ᵗ Fˣ)) := by
  obtain ⟨sk, rfl⟩ := hg.surjective pk
  have h := sigma_hvzk g hg.injective (sk • g) sk (by simp)
  refine (h.map Prod.fst).symm.trans ?_
  rw [realTranscript_eq]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  exact EvalDistEq.bind_right _ fun a => EvalDistEq.bind_const ($ᵗ F) _

theorem sigma_simCommitPredictability (g : G)
    (hg : Function.Bijective (fun x : F => x • g)) :
    (sigma g).simCommitPredictability (simTranscript (F := F) g)
      ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ := by
  classical
  intro pk R
  rw [← prEvent_map (simTranscript g pk) Prod.fst (fun x => x = R),
    (sim_commit g hg pk).prEvent_eq]
  have hinj : Function.Injective (fun a : Fˣ => (a : F) • g) :=
    hg.injective.comp Units.val_injective
  by_cases hR : ∃ a : Fˣ, (a : F) • g = R
  · obtain ⟨a, rfl⟩ := hR
    rw [prEvent_map_injective ($ᵗ Fˣ) hinj a, SampleableType.prEvent_uniformSample_eq_singleton,
      Fintype.card_units]
  · have hz : Pr{let x ← (fun a : Fˣ => (a : F) • g) <$> ($ᵗ Fˣ)}[x = R] = 0 := by
      apply (prEvent_eq_zero_of_not_mem_support _)
      simpa only [support_map, Set.mem_image, not_exists, not_and] using
        (fun a _ ha => hR ⟨a, ha⟩)
    rw [hz]
    exact zero_le

variable [DecidableEq M]

omit [Fintype F] [DecidableEq F] [DecidableEq M] in
theorem game_eq_advantage (g : G) (adv : Adversary (F := F) (M := M) g) :
    𝒟[game g adv] {true} =
      SignatureAlg.unforgeableAdvantage (FiatShamir.runtime (Commit := G) (Chal := F) M) adv := by
  rw [SignatureAlg.unforgeableAdvantage, FiatShamir.runtime_eq_runtimeWithCache_empty,
    FiatShamir.runtimeWithCache_evalDist]
  unfold game
  congr!

/-- The actual Fiat-Shamir reduction uses the finite nonzero-nonce simulator. -/
def dlogReduction (g : G) (adv : Adversary (F := F) (M := M) g) (qH : Nat) :
    DLogAdversary F G :=
  letI : Inhabited F := ⟨0⟩
  fun _ pk => FiatShamir.cmaReduction (sigma g) (dlogGenerable F g) M
    (simTranscript g) adv qH pk

/-- Nonzero-nonce EUF-CMA success implies success of the named discrete-log solver.
Both adversary query bounds hold for every public key and every reply path. -/
theorem security (g : G) (hg : Function.Bijective (fun x : F => x • g))
    (adv : Adversary (F := F) (M := M) g) (qS qH : Nat)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    let eps := 𝒟[game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[dlogExperiment g (dlogReduction g adv qH)] {true} := by
  let : Inhabited F := ⟨0⟩
  let : Finite G := Finite.of_surjective _ hg.surjective
  have hred := FiatShamir.euf_cma_bound (sigma g) (dlogGenerable F g) M
    (sigma_speciallySound g) (simTranscript g) (ζ_zk := 0)
    ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp
      (sigma_hvzk g hg.injective))
    (β := ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹)
    (sigma_simCommitPredictability g hg) adv qS qH hQ
  have hexp :
      Pr{let x ← (hardRelationExperiment (dlogGenerable F g)
        (FiatShamir.cmaReduction (sigma g) (dlogGenerable F g) M
          (simTranscript g) adv qH))}[x = true] =
        Pr{let x ← dlogExperiment g (dlogReduction g adv qH)}[x = true] := by
    rw [show Pr{let x ← (hardRelationExperiment (dlogGenerable F g)
        (FiatShamir.cmaReduction (sigma g) (dlogGenerable F g) M
          (simTranscript g) adv qH))}[x = true] =
        Pr{let y ← (do
          let x ← $ᵗ F
          let w ← FiatShamir.cmaReduction (sigma g) (dlogGenerable F g) M
            (simTranscript g) adv qH (x • g)
          pure (decide (w • g = x • g)))}[y = true] by
      simp [hardRelationExperiment, dlogGenerable]]
    simp [dlogExperiment, dlogReduction, prEvent_norm, hg.injective.eq_iff]
  rw [game_eq_advantage, ← prEvent_eq_evalDist_singleton, ← hexp]
  simpa only [mul_zero, zero_add, FiatShamir.challengeSpaceInv, signature, FiatShamir.inROM]
    using hred

end Schnorr.NonzeroNonce
