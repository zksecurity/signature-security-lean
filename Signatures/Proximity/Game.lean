import Signatures.Model.PairingCurve
import Signatures.Proximity.Spec.LazyAGM
import Signatures.Model.DirectAGM

/-! Proximity security games, independent of any execution model or resource certificate.
`signature` is the Proximity scheme as a pairing-family scheme: the hash of a vector
on a slot is `H(none, slot) + Σ vₖ • H(k, slot)` over the shared lazy oracle, and `agm`
is the shared EUF-CMA experiment (`Model.EufCma.game`) at it for algebraic attackers.
`collision` observes the fresh-collision event the bound charges for.
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

/-- Proximity: secret `x`, public key `x • g₂`, signature `x • H(v, slot)` with
`H(v, slot) = H₀(none, slot) + Σ vₖ • H₀(k, slot)`, verification `e(σ, g₂) = e(H(v, slot), pk)`. -/
noncomputable def signature : EufCma.Scheme (Option (Fin dimension) × Slot) 𝔾₁ ((Fin dimension → 𝔽) × Slot)
    (curve.KeyGroup securityParameter) 𝔽 𝔾₁ :=
  DirectAGM.scheme (Gₜ := 𝔾ₜ) LazyAGM.terms g₂

/-- Algebraic attackers, run through the explanation-checking interaction from `g₁`. -/
noncomputable instance : EufCma.Attacker (AlgebraicAdversary curve securityParameter dimension (Slot := Slot))
    (Option (Fin dimension) × Slot) 𝔾₁ ((Fin dimension → 𝔽) × Slot) (curve.KeyGroup securityParameter) 𝔾₁ :=
  DirectAGM.attacker g₁

/-- A win requires validity and freshness. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter dimension (Slot := Slot)) : ProbComp Bool :=
  EufCma.game (signature curve securityParameter dimension (Slot := Slot)) adversary

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
