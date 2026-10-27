import Signatures.Model.PairingCurve
import Signatures.Model.EufCma

/-! Synchronized Pointcheval–Sanders signatures. All signers of a period `t` share the hash
`H(t) ∈ 𝔾₁`; a signer's share on `m` is `(x + y·m) • H(t)`, and shares of one period aggregate
by addition. The experiment attacks one honest key: a forgery is a `Bundle` naming the
co-signers' keys and messages with the aggregate, verified against the honest key and all
of them, on a period/message the honest signer never signed, with at most one honest
signature per period (`onePerPeriod`). The algebraic game awaits the key-registration rule
for co-signer keys; security bounds are not stated yet. -/

open OracleComp OracleSpec Model

namespace SynchronizedPS

/-- An aggregate signature together with the other signers' keys and messages. -/
structure Bundle (F G₁ G₂ : Type) where
  others : List ((G₂ × G₂) × F)
  aggregate : G₁

namespace Game

variable (curve : Model.PairingCurve) (securityParameter : Nat) {Period : Type} [DecidableEq Period]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾₂" => curve.KeyGroup securityParameter
local notation "g₂" => curve.keyGenerator securityParameter
/-- The pairing `e : 𝔾₁ × 𝔾₂ → 𝔾ₜ`. -/
local notation "e(" a ", " b ")" =>
  BilinearGroup.pairing (F := curve.Scalar securityParameter) (Gₜ := curve.TargetGroup securityParameter) a b

/-- An ordinary attacker: a program from the honest public key with coins, period hashing
and signing access, ending in a period, message and bundle. -/
abbrev UnrestrictedAdversary := curve.KeyGroup securityParameter × curve.KeyGroup securityParameter →
  OracleComp (RandomOracle.Spec Period (curve.SignatureGroup securityParameter) +
      ((Period × curve.Scalar securityParameter) →ₒ
        Bundle (curve.Scalar securityParameter) (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)))
    ((Period × curve.Scalar securityParameter) ×
      Bundle (curve.Scalar securityParameter) (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter))

/-- The honest signer's share at period `t` on `m` is `(x + y·m) • H(t)`; a bundle verifies
when `e(H(t), Σ (Xᵢ + mᵢ • Yᵢ)) = e(aggregate, g₂)` over the honest key and the co-signers. -/
noncomputable def signature : EufCma.Scheme Period 𝔾₁ (Period × 𝔽) (𝔾₂ × 𝔾₂) (𝔽 × 𝔽) (Bundle 𝔽 𝔾₁ 𝔾₂) where
  keygen := do
    let x ← RandomOracle.sample 𝔽
    let y ← RandomOracle.sample 𝔽
    return ((x • g₂, y • g₂), (x, y))
  sign _ secret message := do
    let hash ← RandomOracle.hash message.1
    return ⟨[], (secret.1 + secret.2 * message.2) • hash⟩
  verify publicKey message bundle := do
    let hash ← RandomOracle.hash message.1
    let keys := (publicKey.1 + message.2 • publicKey.2) +
      (bundle.others.map fun signer => signer.1.1 + signer.2 • signer.1.2).sum
    return decide (hash ≠ 0 ∧ e(hash, keys) = e(bundle.aggregate, g₂))

/-- The honest signer signs at most once per period. -/
def onePerPeriod (_message : Period × 𝔽) (signed : List (Period × 𝔽)) : Prop :=
  signed.Pairwise fun first second => first.1 ≠ second.1

instance (message : Period × 𝔽) (signed : List (Period × 𝔽)) : Decidable (onePerPeriod curve securityParameter message signed) := by
  unfold onePerPeriod
  infer_instance

/-- Synchronized unforgeability for an ordinary attacker. -/
noncomputable def eufCma (adversary : UnrestrictedAdversary curve securityParameter (Period := Period)) : ProbComp Bool :=
  EufCma.game (signature curve securityParameter (Period := Period))
    (⟨adversary⟩ : EufCma.Adversary (signature curve securityParameter (Period := Period)))
    (onePerPeriod curve securityParameter)

end Game
end SynchronizedPS
