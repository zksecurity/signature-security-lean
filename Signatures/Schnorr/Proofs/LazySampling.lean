import Signatures.Schnorr.LazyROMReduction
import VCVio.OracleComp.EvalDist.UniformCompatibility

/-! Explicit native-measure correspondence for interpreting the two Schnorr
fork oracle families as private uniform draws and fresh scalar challenges. -/

open OracleComp OracleSpec MeasureTheory

namespace Schnorr.LazyROM

variable {F A : Type} [SampleableType F] [Fintype F] [Inhabited F]

noncomputable local instance samplingUniformChallenges : IsUniformSpec (Unit →ₒ F) :=
  IsUniformSpec.ofFintypeInhabited _

variable [MeasurableSpace F] [DiscreteMeasurableSpace F] [MeasurableSpace A]

noncomputable local instance samplingNativeMeasure : IsUniformMeasureSpec (unifSpec + (Unit →ₒ F)) :=
  OracleSpec.instIsUniformMeasureSpecOfIsUniformSpec

/-- Sampling the two families preserves every measurable output event. The
statement compares native measures on both sides; the discrete proof kernel
is used only through the explicit uniform-compatibility theorem. -/
theorem sample_measure (program : OracleComp (unifSpec + (Unit →ₒ F)) A) :
    𝒟[simulateQ sample program] = 𝒟[program] := by
  apply Measure.ext
  intro event measurable
  rw [evalDist_apply _ measurable, evalDist_apply _ measurable]
  apply probEvent_congr' (fun _ _ => Iff.rfl)
  apply OracleComp.evalSPMF_simulateQ_eq_evalSPMF
  intro i
  cases i with
  | inl n =>
      apply evalSPMF_ext
      intro answer
      simp only [sample, QueryImpl.add_apply_inl, QueryImpl.ofLift_eq_id',
        QueryImpl.id'_apply, probOutput_query, ← Nat.card_eq_fintype_card]
      rfl
  | inr u =>
      apply evalSPMF_ext
      intro answer
      simp [sample, QueryImpl.add_apply_inr, uniformSampleImpl, probOutput_query,
        ← Nat.card_eq_fintype_card]

end Schnorr.LazyROM
