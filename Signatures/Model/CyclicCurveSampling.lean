import Signatures.Model.CyclicCurve

/-! The mathematical curve already supplies a uniform scalar sampler and a
bijection to the group. Transport gives the source ROM game's group sampler
without an extra finite-group enumeration assumption. -/

namespace Model

noncomputable instance (priority := 100) CyclicCurve.groupSampling (curve : CyclicCurve) (n : Nat) :
    SampleableType (curve.Group n) :=
  SampleableType.ofEquiv (Equiv.ofBijective (fun x : curve.Scalar n => x • curve.generator n) (curve.generates n))

end Model
