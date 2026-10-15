import VCVio.OracleComp.EvalDist.UniformCompatibility

/-! Explicit transport from the pinned seeded-fork library's discrete
interpretation to the native uniform-oracle measure interpretation. -/

open OracleComp OracleSpec MeasureTheory

namespace Signatures.Runtime.SeededDeferred

variable {I A : Type} {spec : OracleSpec I}
  [∀ i, MeasurableSpace (spec.Range i)] [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [IsUniformSpec spec] [MeasurableSpace A]

theorem measure_of_compat {left right : OracleComp spec A}
    (h : @evalDist (OracleComp spec) instEvalDistSemanticsOfMonadLiftTSPMF A _ left =
      @evalDist (OracleComp spec) instEvalDistSemanticsOfMonadLiftTSPMF A _ right) :
    𝒟[left] = 𝒟[right] := by
  apply Measure.ext
  intro event hevent
  have he := congrArg (fun μ : Measure A => μ event) h
  simpa only [evalDist_apply, hevent] using he

end Signatures.Runtime.SeededDeferred
