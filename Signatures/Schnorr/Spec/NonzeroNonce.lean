import Signatures.Schnorr.Spec.ROM

/-!
The nonzero-nonce convention of Pointcheval--Stern (JoC 2000, Section 3.2.2).
This variant is separate from the full-field scheme used in the existing ROM
theorem and in Fuchsbauer--Plouviez--Seurin (EUROCRYPT 2020, Figure 3).
Only nonce sampling changes here. The separate NonzeroNonce proof supplies its
simulator law and security theorem; the full-field proof is not transferred implicitly.
-/

open OracleComp OracleSpec

namespace Schnorr.NonzeroNonce

variable {F G M : Type} [Field F] [SampleableType F] [SampleableType Fˣ]
  [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G] [DecidableEq M]

/-- Schnorr with a nonzero nonce and the full scalar challenge space. -/
def sigma (g : G) : SigmaProtocol G F G F F F (fun pk sk => decide (sk • g = pk)) :=
  { Schnorr.sigma F G g with
    commit := fun _ _ => do
      let a ← $ᵗ Fˣ
      pure ((a : F) • g, (a : F))
    sim := fun _ => (fun a : Fˣ => (a : F) • g) <$> ($ᵗ Fˣ) }

/-- Uniform nonzero nonces, with the existing public-key and verification conventions. -/
def signature (g : G) :
    SignatureAlg (OracleComp (unifSpec + (M × G →ₒ F))) M G F (G × F) :=
  FiatShamir (sigma g) (DiffieHellman.dlogGenerable F g) M

omit [DecidableEq M] in
/-- This is exactly the original nonzero-nonce signing algorithm. -/
theorem signature_sign (g pk : G) (x : F) (m : M) :
    (signature g).sign pk x m = (do
      let a ← liftComp ($ᵗ Fˣ) (unifSpec + (M × G →ₒ F))
      let R := (a : F) • g
      let c ← (unifSpec + (M × G →ₒ F)).query (.inr (m, R))
      pure (R, (a : F) + c * x)) := by
  simp [signature, sigma, Schnorr.sigma, FiatShamir, monad_norm,
    OracleComp.liftM_eq_liftM_liftM]

/-- A finite exact simulator. If the usual simulated commitment is zero, a
fresh nonzero scalar repairs it and shifts the response by the same amount.
All samples and group operations depend only on the public key. -/
def simTranscript (g pk : G) : ProbComp (G × F × F) := do
  let c ← $ᵗ F
  let z ← $ᵗ F
  let a ← $ᵗ Fˣ
  let R := z • g - c • pk
  if R = 0 then pure ((a : F) • g, c, z + a)
  else pure (R, c, z)

abbrev Adversary (g : G) := SignatureAlg.UnforgeableAdversary (signature (F := F) (M := M) g)

/-- Adaptive EUF-CMA with one shared lazy cache and nonzero signing nonces. -/
noncomputable def game (g : G) (adv : Adversary (F := F) (M := M) g) : ProbComp Bool := by
  classical
  letI : DecidableEq (M × G) := Classical.decEq _
  exact (simulateQ (M × G →ₒ F).romImpl (SignatureAlg.unforgeableExperiment adv)).run' ∅

omit [SampleableType F] [SampleableType Fˣ] [SampleableType G] [DecidableEq G]
  [DecidableEq M] in
/-- Honest signatures satisfy verification for every nonce and challenge. -/
theorem verifies (g : G) (a : Fˣ) (x c : F) :
    ((a : F) + c * x) • g = (a : F) • g + c • (x • g) := by
  rw [add_smul, mul_smul]

omit [SampleableType F] [SampleableType Fˣ] [SampleableType G] [DecidableEq G]
  [DecidableEq M] in
/-- The commitment can never be the identity when scalar multiplication by g is injective. -/
theorem commitment_ne_zero (g : G)
    (hg : Function.Injective (fun x : F => x • g)) (a : Fˣ) : (a : F) • g ≠ 0 := by
  intro h
  exact Units.ne_zero a (hg (h.trans (zero_smul F g).symm))

end Schnorr.NonzeroNonce
