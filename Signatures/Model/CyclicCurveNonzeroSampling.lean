import Signatures.Model.CyclicCurveSampling
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! A semantic uniform sampler for nonzero scalars of a finite curve. Actual
sampling code and its runtime remain explicit contracts of the execution model. -/

namespace Model

noncomputable instance (priority := 100) CyclicCurve.nonzeroScalarSampling (curve : CyclicCurve) (n : Nat) :
    SampleableType (curve.Scalar n)ˣ := SampleableType.ofFintype _

end Model
