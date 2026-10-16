import Signatures.Model.PairingCurve
import Signatures.BLS.Spec.LazyAGM
import Signatures.BLS.CoCDH.Spec.LazyGame

/-! BLS security games, independent of any execution model or resource certificate.
Read the experiment below as: sample a key, run the attacker with adaptive
hash/signing access, then accept a valid forgery on an unsigned message.
One initially empty lazy oracle is shared by hashing, signing and verification.
Oracle dispatch and algebraic explanation bookkeeping are in the imported spec.
Security bounds are in `Statement.lean`; execution contracts remain separate. -/

open OracleComp OracleSpec

namespace BLS.Game

variable (curve : Model.PairingCurve) (securityParameter : Nat)
  {Message : Type} [DecidableEq Message]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾ₜ" => curve.TargetGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter

/-- Arbitrary internal computation with algebraic group outputs. -/
abbrev AlgebraicAdversary := Model.LazyAGM.Adversary (curve.Scalar securityParameter)
  Message Message (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- Arbitrary message/signature output, without algebraic explanations. -/
abbrev UnrestrictedAdversary := CoCDH.Tight.TightAdvPK Message
  (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- A win requires validity and freshness. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter (Message := Message)) : ProbComp Bool := by
  classical
  exact (simulateQ Model.LazyAGM.lazyImpl (do
    let secret ← (liftM ($ᵗ 𝔽) : OracleComp (Model.LazyAGM.baseSpec Message 𝔾₁) 𝔽)
    let result ← Model.LazyAGM.interactiveRun LazyAGM.terms secret adversary g₁ (secret • g₂)
    match result.data, result.groups .signature with
    | some (forgery, signedMessages), [signature] =>
        let hash : 𝔾₁ ← liftM ((Model.LazyAGM.baseSpec Message 𝔾₁).query (.inr forgery.mstar))
        return decide (
          AlgebraicGroupModel.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) signature g₂ =
            AlgebraicGroupModel.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) hash (secret • g₂) ∧
          forgery.mstar ∉ signedMessages)
    | _, _ => return false)).run' ∅

/-- Ordinary ROM: no algebraic explanation is requested. -/
noncomputable def rom
    (adversary : UnrestrictedAdversary curve securityParameter (Message := Message)) : ProbComp Bool := by
  classical
  exact do
    let secret ← ($ᵗ 𝔽 : ProbComp 𝔽)
    let ((message, signature), state) ←
      (simulateQ (CoCDH.Tight.realOracle (F := 𝔽) g₁ (secret • g₁))
        (CoCDH.Tight.cacheForgeryPK adversary (secret • g₂))).run ((fun _ => none), ∅)
    return decide (AlgebraicGroupModel.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) signature g₂ =
      AlgebraicGroupModel.pairing (F := 𝔽) (Gₜ := 𝔾ₜ)
        (((state.1 message).getD 0) • g₁) (secret • g₂)) && decide (message ∉ state.2)

end BLS.Game
