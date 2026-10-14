import Signatures.Schnorr.Proofs.NonzeroNonce

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
    𝒮[Prod.fst <$> simTranscript (F := F) g pk] =
      𝒮[(fun a : Fˣ => (a : F) • g) <$> ($ᵗ Fˣ)] := by
  obtain ⟨sk, rfl⟩ := hg.surjective pk
  have h := sigma_hvzk g hg.injective (sk • g) sk (by simp)
  have hm := congrArg (Functor.map (Prod.fst : G × F × F → G)) h
  rw [← evalSPMF_map, ← evalSPMF_map, realTranscript_eq] at hm
  rw [← hm]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  apply evalSPMF_bind_congr_left
  intro a
  exact evalSPMF_bind_const_neverFails ($ᵗ F) (by simp) _

theorem sigma_simCommitPredictability (g : G)
    (hg : Function.Bijective (fun x : F => x • g)) :
    (sigma g).simCommitPredictability (simTranscript (F := F) g)
      ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ := by
  classical
  intro pk R
  rw [probOutput_def, sim_commit g hg, ← probOutput_def]
  have hinj : Function.Injective (fun a : Fˣ => (a : F) • g) :=
    hg.injective.comp Units.val_injective
  by_cases hR : ∃ a : Fˣ, (a : F) • g = R
  · obtain ⟨a, rfl⟩ := hR
    rw [probOutput_map_injective ($ᵗ Fˣ) hinj a, probOutput_uniformSample,
      Fintype.card_units]
  · have hz : Pr[= R | (fun a : Fˣ => (a : F) • g) <$> ($ᵗ Fˣ)] = 0 := by
      apply probOutput_eq_zero_of_not_mem_support
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
    (sigma_speciallySound g) (by intro c₁ z₁ c₂ z₂; simp [sigma, Schnorr.sigma])
    (simTranscript g) (ζ_zk := 0) le_rfl
    ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp
      (sigma_hvzk g hg.injective))
    (β := ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹)
    (sigma_simCommitPredictability g hg) adv qS qH hQ
  have hexp :
      Pr[= true | hardRelationExperiment (dlogGenerable F g)
        (FiatShamir.cmaReduction (sigma g) (dlogGenerable F g) M
          (simTranscript g) adv qH)] =
        Pr[= true | dlogExperiment g (dlogReduction g adv qH)] := by
    simp only [hardRelationExperiment, dlogGenerable, dlogExperiment, dlogReduction,
      bind_pure_comp, bind_map_left]
    apply probOutput_bind_congr' _ true
    intro x
    simp only [hg.injective.eq_iff]
  rw [game_eq_advantage]
  simpa only [mul_zero, ENNReal.ofReal_zero, zero_add, FiatShamir.challengeSpaceInv,
    evalDist_apply_singleton, hexp, dlogReduction, signature, FiatShamir.inROM] using hred

end Schnorr.NonzeroNonce
