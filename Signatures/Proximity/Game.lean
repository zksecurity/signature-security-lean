import Signatures.Model.PairingCurve
import Signatures.Proximity.Spec.LazyAGM

/-! Proximity security games, independent of any execution model or resource certificate.
Read the experiment below as: sample a key, run the attacker with adaptive
hash/signing access, then accept a valid forgery on an unsigned message.
One initially empty lazy oracle is shared by hashing, signing and verification.
Oracle dispatch and algebraic explanation bookkeeping are in the imported spec.
Security bounds are in `Statement.lean`; execution contracts remain separate. -/

open OracleComp OracleSpec

namespace Proximity.Game

variable (curve : Model.PairingCurve) (securityParameter dimension : Nat)
  {Slot : Type} [DecidableEq Slot]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾ₜ" => curve.TargetGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter

/-- Arbitrary internal computation with algebraic group outputs. -/
abbrev AlgebraicAdversary := Model.LazyAGM.Adversary (curve.Scalar securityParameter)
  (Option (Fin dimension) × Slot) ((Fin dimension → curve.Scalar securityParameter) × Slot) (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- A win requires validity and freshness. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter dimension (Slot := Slot)) : ProbComp Bool := by
  classical
  exact (simulateQ Model.LazyAGM.lazyImpl (do
    let secret ← (liftM ($ᵗ 𝔽) : OracleComp (Model.LazyAGM.baseSpec (Option (Fin dimension) × Slot) 𝔾₁) 𝔽)
    let result ← Model.LazyAGM.interactiveRun (LazyAGM.terms) secret adversary g₁ (secret • g₂)
    match result.data, result.groups .signature with
    | some (forgery, signedMessages), [signature] =>
        let target ← Model.LazyAGM.evalTerms (LazyAGM.terms forgery.mstar)
        return decide (
          BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) signature g₂ =
            BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) target (secret • g₂) ∧
          forgery.mstar ∉ signedMessages)
    | _, _ => return false)).run' ∅

/-- Observe the original fresh-collision event; it is not a rejection rule. -/
noncomputable def collision
    (adversary : AlgebraicAdversary curve securityParameter dimension (Slot := Slot)) : ProbComp Bool := by
  classical
  exact (simulateQ Model.LazyAGM.lazyImpl (do
    let secret ← (liftM ($ᵗ 𝔽) : OracleComp (Model.LazyAGM.baseSpec (Option (Fin dimension) × Slot) 𝔾₁) 𝔽)
    let (out, transcript) ← Model.LazyAGM.run LazyAGM.terms secret adversary (secret • g₂)
    let signed := transcript.2.map Prod.fst
    return decide (out.mstar ∉ signed ∧
      out.mstar.1 = fun k => (signed.mapIdx fun n m =>
        Model.LazyAGM.tokenCoeff out.ξ n * m.1 k).sum))).run' ∅

end Proximity.Game
