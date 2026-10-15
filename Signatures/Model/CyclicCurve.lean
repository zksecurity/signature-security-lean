import Signatures.Schnorr.Spec.ROM

/-! Mathematical curve data for single-group signature statements. The security
parameter selects the field, group and generator. Execution resources and
hardness are separate; no pairing or finite message domain is required. -/

namespace Model

structure CyclicCurve where
  Scalar : Nat → Type
  Group : Nat → Type
  [scalarField : ∀ n, Field (Scalar n)]
  [scalarSampling : ∀ n, SampleableType (Scalar n)]
  [scalarFinite : ∀ n, Fintype (Scalar n)]
  [scalarEquality : ∀ n, DecidableEq (Scalar n)]
  [group : ∀ n, AddCommGroup (Group n)]
  [module : ∀ n, Module (Scalar n) (Group n)]
  [groupEquality : ∀ n, DecidableEq (Group n)]
  generator : ∀ n, Group n
  generates : ∀ n, Function.Bijective (fun x : Scalar n => x • generator n)

attribute [instance] CyclicCurve.scalarField CyclicCurve.scalarSampling CyclicCurve.scalarFinite
  CyclicCurve.scalarEquality CyclicCurve.group CyclicCurve.module CyclicCurve.groupEquality

def CyclicCurve.order (curve : CyclicCurve) (securityParameter : Nat) : Nat :=
  Fintype.card (curve.Scalar securityParameter)

end Model
