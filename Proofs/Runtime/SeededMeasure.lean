import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.EvalDist.AnswerMeasure

/-! Equality in distribution of seeded-fork computations gives equal output measures. -/

open OracleComp OracleSpec MeasureTheory

namespace Signatures.Runtime.SeededDeferred

variable {I A : Type} {spec : OracleSpec I}
  [OracleSpec.UniformAnswerMeasure spec] [MeasurableSpace A]

theorem measure_of_compat {left right : OracleComp spec A} (h : left =ᵈ right) :
    𝒟[left] = 𝒟[right] :=
  h.evalDist_eq

end Signatures.Runtime.SeededDeferred
