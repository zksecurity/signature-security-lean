import Signatures.Model.CyclicCurveNonzeroSampling
import Signatures.Schnorr.Spec.AGM
import Signatures.Schnorr.Spec.NonzeroNonce

/-! Schnorr EUF-CMA games without execution contracts or resource certificates.
The attacker receives the public key and adaptive hash/signing access. A win is
a valid signature on an unsigned message. Hashing, signing and verification use
one initially empty lazy random oracle. Full-field and nonzero nonces are separate
schemes; only the AGM route requires algebraic explanations.

`signature` and `NonzeroNonce.signature` specify key generation, signing and
verification. `Spec/AGM.lean` handles algebraic messages and malformed requests.
The security bounds are in `Statement.lean`; machine costs remain separate. -/

open OracleComp OracleSpec

namespace Schnorr.Game

variable (curve : Model.CyclicCurve) (securityParameter : Nat)
  {Message : Type} [DecidableEq Message]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾" => curve.Group securityParameter
local notation "g" => curve.generator securityParameter

/-- A public-key-indexed oracle computation returning an arbitrary forgery. -/
abbrev UnrestrictedAdversary := 𝔾 → OracleComp (ROM.advSpec 𝔽 𝔾 Message) (Message × (𝔾 × 𝔽))

/-- Arbitrary internal computation with explained group requests and output. -/
abbrev AlgebraicAdversary := AGM.Adversary 𝔽 𝔾 Message

/-- Ordinary Schnorr, with full-field signing nonces. -/
noncomputable def rom
    (adversary : UnrestrictedAdversary curve securityParameter (Message := Message)) : ProbComp Bool := by
  classical
  letI : DecidableEq (Message × 𝔾) := Classical.decEq _
  let scheme := signature 𝔽 𝔾 g Message
  exact (simulateQ (Message × 𝔾 →ₒ 𝔽).romImpl (do
    let (publicKey, secretKey) ← scheme.keygen
    let ((message, signature), signed) ← scheme.runWithSigningOracle publicKey secretKey (adversary publicKey)
    let valid ← scheme.verify publicKey message signature
    return !signed.wasQueried message && valid)).run' ∅

/-- The same winning condition with uniformly sampled nonzero signing nonces. -/
noncomputable def nonzeroRom
    (adversary : UnrestrictedAdversary curve securityParameter (Message := Message)) : ProbComp Bool := by
  classical
  letI : DecidableEq (Message × 𝔾) := Classical.decEq _
  let scheme := NonzeroNonce.signature (F := 𝔽) (M := Message) g
  exact (simulateQ (Message × 𝔾 →ₒ 𝔽).romImpl (do
    let (publicKey, secretKey) ← scheme.keygen
    let ((message, signature), signed) ← scheme.runWithSigningOracle publicKey secretKey (adversary publicKey)
    let valid ← scheme.verify publicKey message signature
    return !signed.wasQueried message && valid)).run' ∅

/-- Algebraic Schnorr: the commitment is an explained group output.
Malformed requests cannot win. The equation and freshness test are unchanged. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) : ProbComp Bool :=
  (simulateQ (unifFwdImpl (Message × 𝔾 →ₒ 𝔽) + randomOracle (spec := Message × 𝔾 →ₒ 𝔽)) (do
    let secret ← liftComp ($ᵗ 𝔽) (AGM.BaseSpec 𝔽 𝔾 Message)
    let ((out, _basis), state) ← (adversary.run (AGM.handler g secret) (AGM.initial g (secret • g))).run {}
    match out.value.groups () with
    | [R] =>
        let (message, z) := out.value.data
        let challenge : 𝔽 ← (AGM.BaseSpec 𝔽 𝔾 Message).query (.inr (message, R))
        return !state.malformed && decide (message ∉ state.signed ∧ z • g = R + challenge • (secret • g))
    | _ => return false)).run' ∅

end Schnorr.Game
