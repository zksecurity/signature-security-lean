import Signatures.Model.PairingCurve
import Signatures.OOPS.Spec.LazyAGM
import Signatures.Model.AlgebraicOracle

/-! OOPS security games, independent of any execution model or resource certificate.
Read the experiment below as: sample a key, run the attacker with adaptive
hash/signing access, then accept a valid forgery on an unsigned message.
One initially empty lazy oracle is shared by hashing, signing and verification.
Oracle dispatch and algebraic explanation bookkeeping are in the imported spec.
Security bounds are in `Statement.lean`; execution contracts remain separate. -/

open OracleComp OracleSpec
open Model

namespace OOPS.Game

variable (curve : Model.PairingCurve) (securityParameter degree : Nat)
  {Topic : Type} [DecidableEq Topic]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾ₜ" => curve.TargetGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter

/-- Arbitrary internal computation with algebraic group outputs. -/
abbrev AlgebraicAdversary := Model.LazyAGM.Adversary (curve.Scalar securityParameter)
  (Topic × Fin (degree + 1)) (curve.Scalar securityParameter × Topic) (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- A win requires validity and freshness. At most `degree` distinct scalar messages may have been signed on the forged topic. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter degree (Topic := Topic)) : ProbComp Bool := by
  classical
  exact RandomOracle.run do
    let secret ← RandomOracle.sample 𝔽
    let forgery ← AlgebraicOracle.run (LazyAGM.terms degree) secret adversary g₁ (secret • g₂)
    let hash ← AlgebraicOracle.hashMessage (LazyAGM.terms degree) forgery.message
    return decide (
      LazyAGM.admissible degree forgery.message forgery.signedMessages ∧
      BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) forgery.signature g₂ =
        BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) hash (secret • g₂) ∧
      forgery.message ∉ forgery.signedMessages)

end OOPS.Game
