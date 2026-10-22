import Signatures.Model.PairingCurve
import Signatures.BLS.Spec.LazyAGM
import Signatures.BLS.Spec.ROM
import Signatures.Model.DirectAGM
import Signatures.Model.EufCma

/-! BLS security games, independent of any execution model or resource certificate.
Read the experiment below as: sample a key, run the attacker with adaptive
hash/signing access, then accept a valid forgery on an unsigned message.
Security bounds are in `Statement.lean`; execution contracts remain separate.

`signature` is BLS as a scheme and `eufCma` is the shared EUF-CMA experiment at
it (`Model.EufCma.game`): the attacker's `random`/`hash` requests pass to one
lazy random oracle `H : Message → 𝔾₁`, started empty and shared with the signer
and the verifier, and `sign m` runs `signature.sign` and records `m`. `rom` is the
same experiment with the hash exponents kept by the oracle (`ROM.oracle`, replies
`ρ_m • g₁` and `ρ_m • (x • g₁)`), the form the co-CDH proof starts from;
`Proofs/EufCma.lean` shows the two have the same distribution because `g₁`
generates. In `agm` the attacker must explain every group element it sends as a
combination of the elements received so far (`g₁`, then each hash and signing
reply in order); requests carry no group arguments and the output is exactly one
`𝔾₁` signature with its explanation, recorded by `wellFormed`, so a malformed run
cannot win. -/

open OracleComp OracleSpec
open Model

namespace BLS.Game

variable (curve : Model.PairingCurve) (securityParameter : Nat)
  {Message : Type} [DecidableEq Message]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾₂" => curve.KeyGroup securityParameter
local notation "𝔾ₜ" => curve.TargetGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter

/-- Arbitrary internal computation with algebraic group outputs. -/
abbrev AlgebraicAdversary := Model.DirectAGM.Adversary (curve.Scalar securityParameter)
  Message Message (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- Arbitrary message/signature output, without algebraic explanations. -/
abbrev UnrestrictedAdversary := ROM.AdversaryPK Message
  (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- BLS itself: the secret key is `x`, the public key `x • g₂`, a signature `x • H(m)`,
and verification checks `e(σ, g₂) = e(H(m), pk)`. -/
noncomputable def signature : EufCma.Scheme Message 𝔾₁ Message 𝔾₂ 𝔽 𝔾₁ where
  keygen := do
    let secret ← RandomOracle.sample 𝔽
    return (secret • g₂, secret)
  sign _ secret message := do
    let hash ← RandomOracle.hash message
    return secret • hash
  verify publicKey message signature := do
    let hash ← RandomOracle.hash message
    return decide (BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) signature g₂ =
      BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) hash publicKey)

/-- Standard EUF-CMA for BLS: the shared experiment at `signature`. -/
noncomputable def eufCma
    (adversary : EufCma.Adversary (signature curve securityParameter (Message := Message))) : ProbComp Bool :=
  EufCma.game adversary

/-- A win requires validity and freshness. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) : ProbComp Bool := by
  classical
  exact RandomOracle.run do
    let secret ← RandomOracle.sample 𝔽
    let forgery ← DirectAGM.run LazyAGM.terms secret adversary g₁ (secret • g₂)
    let hash ← RandomOracle.hash forgery.message
    return decide (forgery.wellFormed ∧
      BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) forgery.signature g₂ =
        BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) hash (secret • g₂) ∧
      forgery.message ∉ forgery.signedMessages)

/-- Ordinary ROM: no algebraic explanation is requested. -/
noncomputable def rom
    (adversary : UnrestrictedAdversary curve securityParameter (Message := Message)) : ProbComp Bool := by
  classical
  exact do
    let secret ← ($ᵗ 𝔽 : ProbComp 𝔽)
    let ((message, valid), state) ←
      (simulateQ (ROM.oracle (F := 𝔽) g₁ (secret • g₁)) (do
        let (message, signature) ← adversary (secret • g₂)
        let hash ← ROM.hash message
        return (message, decide (
          BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) signature g₂ =
            BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) hash (secret • g₂))))).run ROM.State.empty
    return valid && decide (message ∉ state.signedMessages)

end BLS.Game
