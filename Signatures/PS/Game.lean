import Signatures.Model.PairingCurve
import Signatures.Model.DirectAGM
import Signatures.Model.EufCma

/-! Pointcheval–Sanders signatures (single message), independent of any execution model.
`signature` is the scheme; `eufCma` and `agm` are the shared EUF-CMA experiment at it for
ordinary and algebraic attackers. There is no hash: a signature is a fresh group element
`h` together with `(x + y·m) • h`, so the shared oracle only supplies coins. Security bounds
are not stated yet. -/

open OracleComp OracleSpec Model

namespace PS.Game

variable (curve : Model.PairingCurve) (securityParameter : Nat)

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾₂" => curve.KeyGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter
/-- The pairing `e : 𝔾₁ × 𝔾₂ → 𝔾ₜ`. -/
local notation "e(" a ", " b ")" =>
  BilinearGroup.pairing (F := curve.Scalar securityParameter) (Gₜ := curve.TargetGroup securityParameter) a b

/-- Arbitrary internal computation with algebraic group outputs; messages are scalars and
there is nothing to hash. -/
abbrev AlgebraicAdversary := Model.DirectAGM.Adversary (curve.Scalar securityParameter) Empty
  (curve.Scalar securityParameter) (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- An ordinary attacker: a program from the public key, with coins and signing access. -/
abbrev UnrestrictedAdversary := curve.KeyGroup securityParameter × curve.KeyGroup securityParameter →
  OracleComp (RandomOracle.Spec Empty (curve.SignatureGroup securityParameter) +
      (curve.Scalar securityParameter →ₒ curve.SignatureGroup securityParameter × curve.SignatureGroup securityParameter))
    (curve.Scalar securityParameter × (curve.SignatureGroup securityParameter × curve.SignatureGroup securityParameter))

/-- Secret key `(x, y)`, public key `(x • g₂, y • g₂)`, a signature `(h, (x + y·m) • h)` for a
fresh `h`, and verification `h ≠ 0 ∧ e(h, X + m • Y) = e(s, g₂)`. -/
noncomputable def signature : EufCma.Scheme Empty 𝔾₁ 𝔽 (𝔾₂ × 𝔾₂) (𝔽 × 𝔽) (𝔾₁ × 𝔾₁) where
  keygen := do
    let x ← RandomOracle.sample 𝔽
    let y ← RandomOracle.sample 𝔽
    return ((x • g₂, y • g₂), (x, y))
  sign _ secret message := do
    let h ← RandomOracle.sample 𝔾₁
    return (h, (secret.1 + secret.2 * message) • h)
  verify publicKey message σ :=
    return decide (σ.1 ≠ 0 ∧ e(σ.1, publicKey.1 + message • publicKey.2) = e(σ.2, g₂))

/-- Algebraic attackers receive `g₁` and both key components, and each signature as two
explained group elements. -/
noncomputable instance : EufCma.Attacker (AlgebraicAdversary curve securityParameter) Empty 𝔾₁ 𝔽 (𝔾₂ × 𝔾₂) (𝔾₁ × 𝔾₁) :=
  DirectAGM.attackerTuple g₁ (fun publicKey => [publicKey.1, publicKey.2]) (fun σ => [σ.1, σ.2])
    (fun | [h, s] => some (h, s) | _ => none)

/-- Standard EUF-CMA for an ordinary attacker. -/
noncomputable def eufCma (adversary : UnrestrictedAdversary curve securityParameter) : ProbComp Bool :=
  EufCma.game (signature curve securityParameter)
    (⟨adversary⟩ : EufCma.Adversary (signature curve securityParameter))

/-- The same experiment for an algebraic attacker. -/
noncomputable def agm (adversary : AlgebraicAdversary curve securityParameter) : ProbComp Bool :=
  EufCma.game (signature curve securityParameter) adversary

end PS.Game
