import Signatures.Model.PairingCurve
import Signatures.BLS.Spec.LazyAGM
import Signatures.BLS.Spec.ROM
import Signatures.Model.DirectAGM

/-! BLS security games, independent of any execution model or resource certificate.
Read the experiment below as: sample a key, run the attacker with adaptive
hash/signing access, then accept a valid forgery on an unsigned message.
Security bounds are in `Statement.lean`; execution contracts remain separate.

How the oracle works. The hash `H : Message → 𝔾₁` is one lazy random oracle,
started empty by `RandomOracle.run`: the first time a message is hashed, by the
attacker, the signer or the final verification, a uniform point of `𝔾₁` is
drawn and remembered, and every later hash of that message returns the same
point. The attacker starts from `(g₁, X)` with `X = x • g₂` and may make three
kinds of request: `random n` draws a uniform element of `Fin (n + 1)`;
`hash m` returns `H(m)`; `sign m` records `m` as signed and returns `x • H(m)`,
which the signer computes through the same shared oracle.

Algebraic bookkeeping in `agm`. Oracle replies are the attacker's only source of
group elements, so its received `𝔾₁` basis is the chronological list `g₁`, then
each hash and signing reply in the order delivered. Every group element the
attacker sends out must come with a coefficient vector over the elements received
so far, and the shared library (`Model.DirectAGM`, `AlgebraicGroupModel.Interaction`)
checks that the vector evaluates to the element. Requests carry no group arguments
(a request that does is marked malformed) and the final output is exactly one
`𝔾₁` signature `σ` with its explanation and no `𝔾₂` element; `wellFormed` records
these conditions, and a malformed run cannot win. The ROM game `rom` asks for no
explanations: `ROM.oracle` keeps a private table of hash exponents `ρ_m`, answers
`hash m` with `ρ_m • g₁` and `sign m` with `ρ_m • (x • g₁) = x • H(m)`, and the
final verification hashes through the same table. -/

open OracleComp OracleSpec
open Model

namespace BLS.Game

variable (curve : Model.PairingCurve) (securityParameter : Nat)
  {Message : Type} [DecidableEq Message]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾ₜ" => curve.TargetGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter

/-- Arbitrary internal computation with algebraic group outputs. -/
abbrev AlgebraicAdversary := Model.DirectAGM.Adversary (curve.Scalar securityParameter)
  Message Message (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- Arbitrary message/signature output, without algebraic explanations. -/
abbrev UnrestrictedAdversary := ROM.AdversaryPK Message
  (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

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
