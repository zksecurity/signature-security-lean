import Signatures.Schnorr.Spec.ROM
import Proofs.Schnorr.FixedTapeExtraction

/-! Schnorr's named fixed-private-tape EUF-CMA reduction. This probability
endpoint makes complete seed coverage explicit. A machine endpoint must derive
that coverage and charge seed generation and both executions. -/

open OracleComp OracleSpec DiffieHellman

namespace Schnorr.FixedTape

variable {F G M : Type} [Field F] [SampleableType F] [Fintype F] [DecidableEq F]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

/-- Full query tree of the simulated CMA adversary, including final verification. -/
abbrev main (g pk : G) (adv : ROM.Adversary (F := F) (M := M) g) :=
  FiatShamir.Fork.runTrace (Schnorr.sigma F G g) (dlogGenerable F g) M
    (FiatShamir.cmaToNmaAdv (Schnorr.sigma F G g) (dlogGenerable F g) M
      (Schnorr.simTranscript F G g) adv) pk

/-- The DLog reduction samples a complete private tape once and retains it in
both runs, including all private draws after the selected hash query. -/
def dlogReduction (g : G) (adv : ROM.Adversary (F := F) (M := M) g)
    (privateFamilies : List Nat) (qR qH : Nat) : DLogAdversary F G :=
  fun _ pk => FiatShamir.FixedTape.cmaReduction (Schnorr.sigma F G g) (dlogGenerable F g) M
    (Schnorr.simTranscript F G g) adv privateFamilies qR qH pk

private theorem hardRelation_dlog (g : G) (hgen : Function.Bijective (fun x : F => x • g))
    (red : G → ProbComp F) :
    Pr[= true | hardRelationExperiment (dlogGenerable F g) red] =
      Pr[= true | dlogExperiment g (fun _ pk => red pk)] := by
  rw [show Pr[= true | hardRelationExperiment (dlogGenerable F g) red] =
      Pr[= true | do
        let x ← $ᵗ F
        let w ← red (x • g)
        pure (decide (w • g = x • g))] by
    simp [hardRelationExperiment, dlogGenerable]]
  exact probOutput_bind_congr' _ true fun x =>
    probOutput_bind_congr' _ true fun sk => by simp [hgen.1.eq_iff]

/-- Fixed-private-tape Schnorr security, with the original signing-simulation
loss and exactly `qH + 1` fork positions. The seed bound covers every reply path,
not merely the first execution's observed private queries. -/
theorem security (g : G) (hgen : Function.Bijective (fun x : F => x • g))
    (adv : ROM.Adversary (F := F) (M := M) g) (privateFamilies : List Nat) (qR qS qH : Nat)
    (hQ : ∀ pk, FiatShamir.signHashQueryBound (M := M) (oa := adv.main pk) qS qH)
    (hseed : ∀ pk, IsPerIndexQueryBound (main g pk adv) (finiteBounds privateFamilies qR (qH + 1))) :
    let eps := 𝒟[ROM.game g adv] {true} -
      (qS : ENNReal) * (qS + qH) * (Fintype.card F : ENNReal)⁻¹
    eps * (eps / (qH + 1 : ENNReal) - (Fintype.card F : ENNReal)⁻¹) ≤
      𝒟[dlogExperiment g (dlogReduction g adv privateFamilies qR qH)] {true} := by
  letI : Inhabited F := ⟨0⟩
  haveI : Finite G := Finite.of_surjective (fun x : F => x • g) hgen.2
  have hred := FiatShamir.FixedTape.euf_cma_bound
    (Schnorr.sigma F G g) (dlogGenerable F g) M (Schnorr.sigma_speciallySound F G g)
    (Schnorr.simTranscript F G g) 0 le_rfl
    ((ChallengeVerifyProtocol.perfectHVZK_iff_hvzk_zero _ _).mp (Schnorr.sigma_hvzk F G g))
    ((Fintype.card F : ENNReal)⁻¹) (Schnorr.sigma_simCommitPredictability F G g hgen)
    adv privateFamilies qR qS qH hQ hseed
  rw [ROM.game_eq_advantage]
  unfold dlogReduction
  simp only [mul_zero, ENNReal.ofReal_zero, zero_add, FiatShamir.challengeSpaceInv] at hred
  simpa only [evalDist_apply_singleton, Schnorr.signature, FiatShamir.inROM] using
    hred.trans_eq (hardRelation_dlog g hgen
      (FiatShamir.FixedTape.cmaReduction (Schnorr.sigma F G g) (dlogGenerable F g) M
        (Schnorr.simTranscript F G g) adv privateFamilies qR qH))

end Schnorr.FixedTape
