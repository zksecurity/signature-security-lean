import Signatures.Model.CyclicCurveNonzeroSampling
import Signatures.Schnorr.Spec.Oracle

/-! Schnorr EUF-CMA games without execution contracts or resource certificates.
All three are the shared EUF-CMA experiment (`Model.EufCma.game`): the attacker
receives the public key and adaptive hash/signing access, and a win is a valid
signature on an unsigned message, with hashing, signing and verification through
one initially empty lazy random oracle. Full-field and nonzero nonces are separate
schemes (`signature`, `NonzeroNonce.signature`); the AGM route is the same
experiment for algebraic attackers (`Spec/Oracle.lean`, `AGM.attacker`).
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

/-- Ordinary Schnorr, with full-field signing nonces: the shared EUF-CMA experiment at
`signature` for an ordinary attacker. -/
noncomputable def rom
    (adversary : UnrestrictedAdversary curve securityParameter (Message := Message)) : ProbComp Bool :=
  EufCma.game (signature 𝔽 𝔾 g Message) (⟨adversary⟩ : EufCma.Adversary (signature 𝔽 𝔾 g Message))

/-- The same experiment with uniformly sampled nonzero signing nonces. -/
noncomputable def nonzeroRom
    (adversary : UnrestrictedAdversary curve securityParameter (Message := Message)) : ProbComp Bool :=
  EufCma.game (NonzeroNonce.signature (F := 𝔽) (M := Message) g)
    (⟨adversary⟩ : EufCma.Adversary (NonzeroNonce.signature (F := 𝔽) (M := Message) g))

/-- Algebraic attackers, run through the explanation-checking interaction from `g`: hash
requests carry an explained commitment, signing replies deliver a new one. -/
noncomputable instance : EufCma.Attacker (AlgebraicAdversary curve securityParameter (Message := Message))
    (Message × 𝔾) 𝔽 Message 𝔾 (𝔾 × 𝔽) :=
  AGM.attacker g

/-- Algebraic Schnorr: the same experiment for an algebraic attacker. Malformed requests,
or an output without exactly one explained commitment, cannot win. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) : ProbComp Bool :=
  EufCma.game (signature 𝔽 𝔾 g Message) adversary

end Schnorr.Game
