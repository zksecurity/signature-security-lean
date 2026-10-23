import Signatures.Model.PairingCurve
import Signatures.OOPS.Spec.LazyAGM
import Signatures.Model.DirectAGM

/-! OOPS security games, independent of any execution model or resource certificate.
`signature` is OOPS as a pairing-family scheme: the hash of a scalar message `c` on
a topic is `Σ cⁱ • H(topic, i)` over the shared lazy oracle, and `agm` is the shared
EUF-CMA experiment (`Model.EufCma.game`) at it for algebraic attackers, with the
target-topic degree rule as the admissibility restriction.
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
abbrev AlgebraicAdversary := Model.DirectAGM.Adversary (curve.Scalar securityParameter)
  (Topic × Fin (degree + 1)) (curve.Scalar securityParameter × Topic) (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- OOPS: secret `x`, public key `x • g₂`, signature `x • H(c, topic)` with
`H(c, topic) = Σ cⁱ • H₀(topic, i)`, verification `e(σ, g₂) = e(H(c, topic), pk)`. -/
noncomputable def signature : EufCma.Scheme (Topic × Fin (degree + 1)) 𝔾₁ (𝔽 × Topic) (curve.KeyGroup securityParameter) 𝔽 𝔾₁ :=
  DirectAGM.scheme (Gₜ := 𝔾ₜ) (LazyAGM.terms degree) g₂

/-- Algebraic attackers, run through the explanation-checking interaction from `g₁`. -/
noncomputable instance : EufCma.Attacker (AlgebraicAdversary curve securityParameter degree (Topic := Topic))
    (Topic × Fin (degree + 1)) 𝔾₁ (𝔽 × Topic) (curve.KeyGroup securityParameter) 𝔾₁ :=
  DirectAGM.attacker g₁

/-- A win requires validity and freshness, and at most `degree` distinct scalar messages
signed on the forged topic. -/
noncomputable def agm
    (adversary : AlgebraicAdversary curve securityParameter degree (Topic := Topic)) : ProbComp Bool :=
  EufCma.game (signature curve securityParameter degree (Topic := Topic)) adversary (LazyAGM.admissible degree)

end OOPS.Game
