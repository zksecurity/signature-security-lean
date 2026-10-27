import Signatures.Model.PairingCurve
import Signatures.Model.EufCma
import Signatures.Model.DirectAGM

/-! Synchronized Pointcheval–Sanders signatures. All signers of a period `t` share the hash
`H(t) ∈ 𝔾₁`; a signer's share on `m` is `(x + y·m) • H(t)`, and shares of one period aggregate
by addition. The experiment attacks one honest key in the certified-key model: a forgery is a
`Bundle` naming the co-signers' key pairs and messages with the aggregate, verified against the
honest key and all of them, on a period/message the honest signer never signed, with at most one
honest signature per period (`onePerPeriod`). `eufCma` and `agm` are the shared EUF-CMA
experiment (`Model.EufCma.game`) for ordinary attackers and for algebraic attackers, which
explain every group element they output from `g₁`, the key's components and the replies received
so far. Security bounds are in `Statement.lean`. -/

open OracleComp OracleSpec Model

namespace SynchronizedPS

/-- An aggregate together with the co-signers' certified key pairs `(x, y)` and messages. -/
structure Bundle (F G₁ : Type) where
  others : List ((F × F) × F)
  aggregate : G₁

/-- What an attacker reports besides the aggregate: the attacked period and message, and the
co-signers' key pairs and messages. -/
abbrev Forgery (F Period : Type) := (Period × F) × List ((F × F) × F)

/-- The honest signer signs at most once per period. -/
def onePerPeriod {F Period : Type} [DecidableEq Period] (_message : Period × F)
    (signed : List (Period × F)) : Prop :=
  signed.Pairwise fun first second => first.1 ≠ second.1

instance {F Period : Type} [DecidableEq Period] (message : Period × F) (signed : List (Period × F)) :
    Decidable (onePerPeriod message signed) := by
  unfold onePerPeriod
  infer_instance

namespace Game

variable (curve : Model.PairingCurve) (securityParameter : Nat) {Period : Type} [DecidableEq Period]

local notation "𝔽" => curve.Scalar securityParameter
local notation "𝔾₁" => curve.SignatureGroup securityParameter
local notation "𝔾₂" => curve.KeyGroup securityParameter
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter
/-- The pairing `e : 𝔾₁ × 𝔾₂ → 𝔾ₜ`. -/
local notation "e(" a ", " b ")" =>
  BilinearGroup.pairing (F := curve.Scalar securityParameter) (Gₜ := curve.TargetGroup securityParameter) a b

/-- Arbitrary internal computation with algebraic group outputs, reporting a `Forgery`. -/
abbrev AlgebraicAdversary := Model.DirectAGM.AdversaryWith (curve.Scalar securityParameter) Period
  (Period × curve.Scalar securityParameter) (Forgery (curve.Scalar securityParameter) Period)
  (curve.SignatureGroup securityParameter) (curve.KeyGroup securityParameter)

/-- An ordinary attacker: a program from the honest public key with coins, period hashing
and signing access, ending in a period, message and bundle. -/
abbrev UnrestrictedAdversary := curve.KeyGroup securityParameter × curve.KeyGroup securityParameter →
  OracleComp (RandomOracle.Spec Period (curve.SignatureGroup securityParameter) +
      ((Period × curve.Scalar securityParameter) →ₒ
        Bundle (curve.Scalar securityParameter) (curve.SignatureGroup securityParameter)))
    ((Period × curve.Scalar securityParameter) ×
      Bundle (curve.Scalar securityParameter) (curve.SignatureGroup securityParameter))

/-- The honest signer's share at period `t` on `m` is `(x + y·m) • H(t)`; a bundle verifies
when `e(H(t), (X + m•Y) + Σ (xᵢ + yᵢ·mᵢ)•g₂) = e(aggregate, g₂)` over the honest key and the
co-signers' certified keys. -/
noncomputable def signature : EufCma.Scheme Period 𝔾₁ (Period × 𝔽) (𝔾₂ × 𝔾₂) (𝔽 × 𝔽) (Bundle 𝔽 𝔾₁) where
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
      (bundle.others.map fun signer => (signer.1.1 + signer.1.2 * signer.2) • g₂).sum
    return decide (e(hash, keys) = e(bundle.aggregate, g₂))

/-- Algebraic attackers, run through the explanation-checking interaction from `g₁` and the
key's two components; the reported data and the explained `𝔾₁` output form the bundle. -/
noncomputable instance : EufCma.Attacker (AlgebraicAdversary curve securityParameter (Period := Period))
    Period 𝔾₁ (Period × 𝔽) (𝔾₂ × 𝔾₂) (Bundle 𝔽 𝔾₁) :=
  DirectAGM.attackerWith g₁ (fun publicKey => [publicKey.1, publicKey.2]) Bundle.aggregate
    (fun forgery aggregate => some (forgery.1, ⟨forgery.2, aggregate⟩))

/-- Synchronized unforgeability for an ordinary attacker. -/
noncomputable def eufCma (adversary : UnrestrictedAdversary curve securityParameter (Period := Period)) : ProbComp Bool :=
  EufCma.game (signature curve securityParameter (Period := Period))
    (⟨adversary⟩ : EufCma.Adversary (signature curve securityParameter (Period := Period)))
    onePerPeriod

/-- The same experiment for an algebraic attacker. -/
noncomputable def agm (adversary : AlgebraicAdversary curve securityParameter (Period := Period)) : ProbComp Bool :=
  EufCma.game (signature curve securityParameter (Period := Period)) adversary onePerPeriod

end Game
end SynchronizedPS
