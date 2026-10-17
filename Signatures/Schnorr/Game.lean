import Signatures.Model.CyclicCurveNonzeroSampling
import Signatures.Schnorr.Spec.Oracle

/-! Schnorr EUF-CMA games without execution contracts or resource certificates.
The attacker receives the public key and adaptive hash/signing access. A win is
a valid signature on an unsigned message. Hashing, signing and verification use
one initially empty lazy random oracle. Full-field and nonzero nonces are separate
schemes; only the AGM route requires algebraic explanations.

`signature` and `NonzeroNonce.signature` specify key generation, signing and
verification. `Spec/Oracle.lean` handles ordinary and algebraic requests with named results.
The security bounds are in `Statement.lean`; machine costs remain separate. -/

open OracleComp OracleSpec
open Model

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
  exact RandomOracle.run do
    let (publicKey, secretKey) ← scheme.keygen
    let forgery ← ROM.run scheme publicKey secretKey (adversary publicKey)
    let challenge ← RandomOracle.hash (forgery.message, forgery.commitment)
    return !forgery.signingLog.wasQueried forgery.message &&
      decide (forgery.response • g = forgery.commitment + challenge • publicKey)

/-- The same winning condition with uniformly sampled nonzero signing nonces. -/
noncomputable def nonzeroRom
    (adversary : UnrestrictedAdversary curve securityParameter (Message := Message)) : ProbComp Bool := by
  classical
  letI : DecidableEq (Message × 𝔾) := Classical.decEq _
  let scheme := NonzeroNonce.signature (F := 𝔽) (M := Message) g
  exact RandomOracle.run do
    let (publicKey, secretKey) ← scheme.keygen
    let forgery ← ROM.run scheme publicKey secretKey (adversary publicKey)
    let challenge ← RandomOracle.hash (forgery.message, forgery.commitment)
    return !forgery.signingLog.wasQueried forgery.message &&
      decide (forgery.response • g = forgery.commitment + challenge • publicKey)

/-- Algebraic Schnorr: the commitment is an explained group output.
Malformed requests cannot win. The equation and freshness test are unchanged. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) : ProbComp Bool :=
  RandomOracle.run do
    let secret ← RandomOracle.sample 𝔽
    let result ← AGM.run g secret adversary
    match result with
    | some forgery =>
        let challenge ← RandomOracle.hash (forgery.message, forgery.commitment)
        return !forgery.state.malformed && decide (
          forgery.message ∉ forgery.state.signedMessages ∧
          forgery.response • g = forgery.commitment + challenge • (secret • g))
    | none => return false

end Schnorr.Game
