import Signatures.Model.PairingCurve
import Signatures.BLS.Spec.LazyAGM
import Signatures.BLS.Spec.ROM
import Signatures.Model.DirectAGM

/-! BLS security games, independent of any execution model or resource certificate.
Read the experiment below as: sample a key, run the attacker with adaptive
hash/signing access, then accept a valid forgery on an unsigned message.
One initially empty lazy oracle is shared by hashing, signing and verification.
Oracle dispatch and algebraic explanation bookkeeping are in the imported spec.
Security bounds are in `Statement.lean`; execution contracts remain separate. -/

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
