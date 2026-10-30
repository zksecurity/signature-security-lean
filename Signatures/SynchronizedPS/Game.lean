import Signatures.Model.PairingCurve
import Signatures.Model.EufCma
import Signatures.Model.DirectAGM

/-! Synchronized Pointcheval–Sanders signatures. All signers of a period `t` share the hash
`H(t) ∈ 𝔾₁`; a signer's share on `m` is `(x + y·m) • H(t)`. The experiment attacks one honest
key: a forgery is a share on a period/message the honest signer never signed, with at most one
honest signature per period (`onePerPeriod`). `eufCma` and `agm` are the shared EUF-CMA
experiment (`Model.EufCma.game`) for ordinary attackers and for algebraic attackers, which
explain every group element they output from `g₁`, the key's components and the replies received
so far. Security bounds are in `Statement.lean`. -/

open OracleComp OracleSpec Model

namespace SynchronizedPS

/-- What an attacker reports besides the signature: the attacked period and message. -/
abbrev Forgery (F Period : Type) := Period × F

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
and signing access, ending in a period, message and signature. -/
abbrev UnrestrictedAdversary := curve.KeyGroup securityParameter × curve.KeyGroup securityParameter →
  OracleComp (RandomOracle.Spec Period (curve.SignatureGroup securityParameter) +
      ((Period × curve.Scalar securityParameter) →ₒ curve.SignatureGroup securityParameter))
    ((Period × curve.Scalar securityParameter) × curve.SignatureGroup securityParameter)

/-- The honest signer's share at period `t` on `m` is `(x + y·m) • H(t)`; a signature verifies
when `e(H(t), X + m•Y) = e(σ, g₂)`. -/
noncomputable def signature : EufCma.Scheme Period 𝔾₁ (Period × 𝔽) (𝔾₂ × 𝔾₂) (𝔽 × 𝔽) 𝔾₁ where
  keygen := do
    let x ← RandomOracle.sample 𝔽
    let y ← RandomOracle.sample 𝔽
    return ((x • g₂, y • g₂), (x, y))
  sign _ secret message := do
    let hash ← RandomOracle.hash message.1
    return (secret.1 + secret.2 * message.2) • hash
  verify publicKey message σ := do
    let hash ← RandomOracle.hash message.1
    return decide (e(hash, publicKey.1 + message.2 • publicKey.2) = e(σ, g₂))

/-- Algebraic attackers, run through the explanation-checking interaction from `g₁` and the
key's two components; the explained `𝔾₁` output is the signature. -/
noncomputable instance : EufCma.Attacker (AlgebraicAdversary curve securityParameter (Period := Period))
    Period 𝔾₁ (Period × 𝔽) (𝔾₂ × 𝔾₂) 𝔾₁ :=
  DirectAGM.attackerWith g₁ (fun publicKey => [publicKey.1, publicKey.2]) id
    (fun forgery signature => some (forgery, signature))

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
