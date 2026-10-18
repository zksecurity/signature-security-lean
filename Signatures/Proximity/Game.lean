import Signatures.Model.PairingCurve
import Signatures.Proximity.Spec.LazyAGM
import Signatures.Model.DirectAGM

/-! Proximity security games, independent of any execution model or resource certificate.
Read the experiment below as: sample a key, run the attacker with adaptive
hash/signing access, then accept a valid forgery on an unsigned message.
One initially empty lazy oracle is shared by hashing, signing and verification.
Oracle dispatch and algebraic explanation bookkeeping are in the imported spec.
Security bounds are in `Statement.lean`; execution contracts remain separate. -/

open OracleComp OracleSpec
open Model

namespace Proximity.Game

variable (curve : Model.PairingCurve) (securityParameter dimension : Nat)
  {Slot : Type} [DecidableEq Slot]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾ₜ" => curve.TargetGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter

/-- Arbitrary internal computation with algebraic group outputs. -/
abbrev AlgebraicAdversary := Model.DirectAGM.Adversary (curve.Scalar securityParameter)
  (Option (Fin dimension) × Slot) ((Fin dimension → curve.Scalar securityParameter) × Slot) (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- A win requires validity and freshness. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter dimension (Slot := Slot)) : ProbComp Bool := by
  classical
  exact RandomOracle.run do
    let secret ← RandomOracle.sample 𝔽
    let forgery ← DirectAGM.run LazyAGM.terms secret adversary g₁ (secret • g₂)
    let hash ← AlgebraicOracle.hashMessage LazyAGM.terms forgery.message
    return decide (forgery.wellFormed ∧
      BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) forgery.signature g₂ =
        BilinearGroup.pairing (F := 𝔽) (Gₜ := 𝔾ₜ) hash (secret • g₂) ∧
      forgery.message ∉ forgery.signedMessages)

/-- Observe the original fresh-collision event; it is not a rejection rule. -/
noncomputable def collision
    (adversary : AlgebraicAdversary curve securityParameter dimension (Slot := Slot)) : ProbComp Bool := by
  classical
  exact RandomOracle.run do
    let secret ← RandomOracle.sample 𝔽
    let forgery ← DirectAGM.run LazyAGM.terms secret adversary g₁ (secret • g₂)
    let (vector, _slot) := forgery.message
    return decide (forgery.message ∉ forgery.signedMessages ∧
      vector = fun k => (forgery.signedMessages.mapIdx fun n (signedVector, _) =>
        Model.LazyAGM.tokenCoeff forgery.signingCoefficients n * signedVector k).sum)

end Proximity.Game
