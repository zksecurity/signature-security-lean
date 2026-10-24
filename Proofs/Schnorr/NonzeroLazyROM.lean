import Proofs.Schnorr.NonzeroLazyROMReduction
import Proofs.Schnorr.NonzeroSecurity
import Proofs.Schnorr.LazyFiatShamir

/-! The nonzero-nonce source game's original probability bound for the named
lazy replaying reduction. Signing collisions cost 1/(|F|-1); fork challenges
still range over all of F. Complete native implementation costs are separate. -/

open OracleComp OracleSpec DiffieHellman

namespace Schnorr.NonzeroNonce.LazyROM

variable {F G M : Type} [Field F] [SampleableType F] [SampleableType Fˣ]
  [DecidableEq F] [AddCommGroup G] [Module F G]
  [SampleableType G] [DecidableEq G] [DecidableEq M]

omit [DecidableEq F] in
/-- The replacement unit draw is private and does not consume a hash slot. -/
theorem main_hashBound (g pk : G) (adv : Adversary (F := F) (M := M) g) (qS qH : Nat)
    (queries : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    IsQueryBoundP (main g pk adv) (· = Sum.inr ()) (qH + 1) :=
  FiatShamir.LazyTape.main_hashBound (sigma g) (dlogGenerable F g) M
    (simTranscript g) adv qS qH queries pk

/-- The generic relation test and the actual DLog equality test coincide. -/
theorem experiment_eq (g : G) (generates : Function.Bijective (fun x : F => x • g))
    (adv : Adversary (F := F) (M := M) g) (qH : Nat) :
    hardRelationExperiment (dlogGenerable F g)
      (FiatShamir.LazyTape.reduction (sigma g) (dlogGenerable F g) M (simTranscript g) adv qH) =
      dlogExperiment g (dlogReduction g adv qH) := by
  simp only [hardRelationExperiment, dlogGenerable, dlogExperiment, dlogReduction,
    bind_pure_comp, bind_map_left]
  congr 1
  funext x
  simp only [generates.injective.eq_iff]

/-- Every ordinary adaptive attacker with the source signing/hash allowances
satisfies the original nonzero-nonce forking bound. No finite message domain,
source language, private-family cover or private-query capacity is required. -/
theorem security [Fintype F] (g : G)
    (generates : Function.Bijective (fun x : F => x • g))
    (adv : Adversary (F := F) (M := M) g) (qS qH : Nat)
    (queries : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH) :
    let eps := 𝒟[game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[dlogExperiment g (dlogReduction g adv qH)] {true} := by
  let : Inhabited F := ⟨0⟩
  let : Finite G := Finite.of_surjective _ generates.surjective
  have h := FiatShamir.LazyTape.security (sigma g) (dlogGenerable F g) M
    (sigma_speciallySound g) (simTranscript g) 0 le_rfl
    ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp (sigma_hvzk g generates.injective))
    (((Fintype.card F - 1 : Nat) : ENNReal)⁻¹) (sigma_simCommitPredictability g generates)
    adv qS qH queries
  rw [experiment_eq g generates adv qH] at h
  rw [game_eq_advantage]
  simpa only [mul_zero, ENNReal.ofReal_zero, zero_add, FiatShamir.challengeSpaceInv,
    signature, FiatShamir.inROM] using h

end Schnorr.NonzeroNonce.LazyROM
