import Proofs.Schnorr.LazyROMReduction
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.EvalDist.AnswerMeasure

/-! Explicit native-measure correspondence for interpreting the two Schnorr
fork oracle families as private uniform draws and fresh scalar challenges. -/

open OracleComp OracleSpec MeasureTheory

namespace Schnorr.LazyROM

variable {F A : Type} [SampleableType F] [Fintype F] [Inhabited F]

noncomputable local instance samplingUniformChallenges : UniformAnswerMeasure (Unit →ₒ F) :=
  UniformAnswerMeasure.ofFiniteNonempty _

variable [MeasurableSpace A]

/-- Sampling the two families preserves every measurable output event. The
statement compares native measures on both sides, with the challenge family
read under its uniform answer measure. -/
theorem sample_measure (program : OracleComp (unifSpec + (Unit →ₒ F)) A) :
    𝒟[simulateQ sample program] = 𝒟[program] := by
  apply evalDist_simulateQ_eq_of_forall
  intro i
  cases i with
  | inl n =>
      simp [sample, QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id', QueryImpl.id'_apply]
  | inr u =>
      let : MeasurableSpace ((unifSpec + (Unit →ₒ F)).Range (.inr u)) := ⊤
      simp only [sample, QueryImpl.add_apply_inr, uniformSampleImpl,
        UniformAnswerMeasure.toMeasure_eq_uniform]
      exact SampleableType.evalDist_uniformSample

end Schnorr.LazyROM
