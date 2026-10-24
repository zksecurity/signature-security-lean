import Proofs.Schnorr.NonzeroSampling

/-! Exact simulation and EUF-CMA security for nonzero Schnorr signing nonces.
Challenges and secret keys still range over the full scalar field. -/

open OracleComp OracleSpec DiffieHellman OracleComp.DeferredSampling
open scoped ENNReal

namespace Schnorr.NonzeroNonce

variable {F G M : Type} [Field F] [SampleableType F] [SampleableType Fˣ]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

theorem sigma_complete (g : G) : (sigma (F := F) g).PerfectlyComplete := by
  intro pk sk h
  rw [evalDist_apply_singleton]
  have heq : sk • g = pk := of_decide_eq_true h
  simp only [sigma, Schnorr.sigma, monad_norm]
  have hv (r c : F) : (r + c * sk) • g = r • g + c • pk := by
    rw [add_smul, mul_smul, heq]
  simp [hv]

theorem sigma_speciallySound (g : G) : (sigma (F := F) g).SpeciallySound :=
  Schnorr.sigma_speciallySound F G g

theorem realTranscript_eq (g pk : G) (sk : F) :
    (sigma g).realTranscript pk sk = (do
      let a ← $ᵗ Fˣ
      let c ← $ᵗ F
      pure ((a : F) • g, c, (a : F) + c * sk)) := by
  simp only [ChallengeVerifyProtocol.realTranscript, sigma, Schnorr.sigma, monad_norm]

variable [DecidableEq F]

omit [SampleableType F] [SampleableType Fˣ] [SampleableType G] in
/-- The repair changes commitment and response together, preserving verification. -/
theorem sim_shift (g : G) (hg : Function.Injective (fun x : F => x • g))
    (sk c r : F) (a : Fˣ) :
    (if (r + c * sk) • g - c • (sk • g) = 0
      then ((a : F) • g, c, r + c * sk + a)
      else ((r + c * sk) • g - c • (sk • g), c, r + c * sk)) =
      (repair r a • g, c, repair r a + c * sk) := by
  have hR : (r + c * sk) • g - c • (sk • g) = r • g := by
    rw [add_smul, mul_smul, add_sub_cancel_right]
  have hz : r • g = 0 ↔ r = 0 := by
    constructor
    · intro h; exact hg (h.trans (zero_smul F g).symm)
    · intro h; simp [h]
  simp only [hR, hz]
  by_cases h : r = 0 <;> simp [repair, h, add_comm]

/-- The finite repair sampler has exactly the honest transcript distribution. -/
theorem sigma_hvzk [Finite F] (g : G)
    (hg : Function.Injective (fun x : F => x • g)) :
    (sigma (F := F) g).PerfectHVZK (simTranscript g) := by
  intro pk sk hsk
  have heq : sk • g = pk := of_decide_eq_true hsk
  subst pk
  rw [realTranscript_eq, evalSPMF_bind_comm]
  unfold simTranscript
  apply evalSPMF_bind_congr_left
  intro c
  rw [← evalSPMF_bind_bijective_add_right_uniform (α := F) id
    Function.bijective_id (c * sk)]
  simpa only [id_eq, ← apply_ite pure, sim_shift g hg] using
    (repair_uniform_bind (fun r => pure (r • g, c, r + c * sk))).symm

end Schnorr.NonzeroNonce
