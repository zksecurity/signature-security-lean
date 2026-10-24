import Proofs.Model.LazyAGM

/-! The mathematical curve data used by pairing-based signature statements.
The security parameter selects the scalar field, groups, pairing, and generators.
Execution models, adversary resources, and query allowances are separate. -/

namespace Model

/-- A family of pairing groups with nondegenerate chosen generators.
This packages the algebraic curve interface; it does not assert a hardness assumption. -/
structure PairingCurve where
  Scalar : Nat → Type
  SignatureGroup : Nat → Type
  KeyGroup : Nat → Type
  TargetGroup : Nat → Type
  [scalarField : ∀ n, Field (Scalar n)]
  [scalarSampling : ∀ n, SampleableType (Scalar n)]
  [scalarFinite : ∀ n, Fintype (Scalar n)]
  [scalarEquality : ∀ n, DecidableEq (Scalar n)]
  [signatureGroup : ∀ n, AddCommGroup (SignatureGroup n)]
  [signatureModule : ∀ n, Module (Scalar n) (SignatureGroup n)]
  [signatureSampling : ∀ n, SampleableType (SignatureGroup n)]
  [signatureFinite : ∀ n, Fintype (SignatureGroup n)]
  [signatureEquality : ∀ n, DecidableEq (SignatureGroup n)]
  [keyGroup : ∀ n, AddCommGroup (KeyGroup n)]
  [keyModule : ∀ n, Module (Scalar n) (KeyGroup n)]
  [keyEquality : ∀ n, DecidableEq (KeyGroup n)]
  [targetGroup : ∀ n, AddCommGroup (TargetGroup n)]
  [targetModule : ∀ n, Module (Scalar n) (TargetGroup n)]
  [targetEquality : ∀ n, DecidableEq (TargetGroup n)]
  [pairing : ∀ n, BilinearGroup.BilinearPairing
    (Scalar n) (SignatureGroup n) (KeyGroup n) (TargetGroup n)]
  generator : ∀ n, SignatureGroup n
  keyGenerator : ∀ n, KeyGroup n
  generates : ∀ n, Function.Bijective (fun r : Scalar n => r • generator n)
  pairingInjective : ∀ n, Function.Injective (fun r : Scalar n =>
    r • (BilinearGroup.pairing (F := Scalar n) (generator n) (keyGenerator n) : TargetGroup n))

attribute [instance] PairingCurve.scalarField PairingCurve.scalarSampling PairingCurve.scalarFinite
  PairingCurve.scalarEquality PairingCurve.signatureGroup PairingCurve.signatureModule
  PairingCurve.signatureSampling PairingCurve.signatureFinite PairingCurve.signatureEquality
  PairingCurve.keyGroup PairingCurve.keyModule PairingCurve.keyEquality
  PairingCurve.targetGroup PairingCurve.targetModule PairingCurve.targetEquality PairingCurve.pairing

/-- The scalar-field order at the selected security parameter. -/
def PairingCurve.order (curve : PairingCurve) (securityParameter : Nat) : Nat :=
  Fintype.card (curve.Scalar securityParameter)

end Model
