import Signatures.Model.PairingCurve
import Signatures.OOPS.Spec.LazyAGM

/-! OOPS security games, independent of any execution model or resource certificate.
Read the experiment below as: sample a key, run the attacker with adaptive
hash/signing access, then accept a valid forgery on an unsigned message.
One initially empty lazy oracle is shared by hashing, signing and verification.
Oracle dispatch and algebraic explanation bookkeeping are in the imported spec.
Security bounds are in `Statement.lean`; execution contracts remain separate. -/

open OracleComp OracleSpec

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
  exact (simulateQ Model.LazyAGM.lazyImpl (do
    let secret ← (liftM ($ᵗ 𝔽) : OracleComp (Model.LazyAGM.baseSpec (Topic × Fin (degree + 1)) 𝔾₁) 𝔽)
    let result ← Model.LazyAGM.interactiveRun (LazyAGM.terms degree) secret adversary g₁ (secret • g₂)
    match result.data, result.groups .signature with
    | some (forgery, signedMessages), [signature] =>
        let target ← Model.LazyAGM.evalTerms (LazyAGM.terms degree forgery.mstar)
        return decide (
          LazyAGM.admissible degree forgery.mstar signedMessages ∧
          BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) signature g₂ =
            BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) target (secret • g₂) ∧
          forgery.mstar ∉ signedMessages)
    | _, _ => return false)).run' ∅

end OOPS.Game
