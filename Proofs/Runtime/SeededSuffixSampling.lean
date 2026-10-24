import Proofs.Runtime.SeededSuffix
import Proofs.Runtime.SeededMeasure

/-! Unused independent seed suffixes can be sampled lazily during the second
run. The retained prefix is arbitrary, so it may be the first run's private
draws together with a replaced challenge. -/

open OracleComp OracleSpec MeasureTheory

namespace Signatures.Runtime.SeededTrace

variable {I A : Type} {spec : OracleSpec I} [DecidableEq I]
  [∀ i, SampleableType (spec.Range i)] [IsUniformSpec spec]
  [∀ i, MeasurableSpace (spec.Range i)] [∀ i, DiscreteMeasurableSpace (spec.Range i)]
  [unifSpec ⊂ₒ spec] [unifSpec ˡ⊂ₒ spec] [MeasurableSpace A]

/-- Appending independent seed entries does not change an adaptive replay's
output law; those entries can instead be sampled by live fallback when needed. -/
theorem generate_suffix_run (main : OracleComp spec A) (budget : I → Nat)
    (families : List I) (recorded : QuerySeed spec) :
    𝒟[do
      let suffix ← liftComp (generateSeed spec budget families) spec
      (simulateQ seededOracle main).run' (append recorded suffix)] =
      𝒟[(simulateQ seededOracle main).run' recorded] := by
  induction families generalizing recorded with
  | nil => simp [append_empty]
  | cons i families ih =>
      simp only [generateSeed_cons, liftComp_bind, liftComp_pure, bind_assoc, pure_bind,
        append_prepend]
      trans 𝒟[do
        let answers ← liftComp (replicate (budget i) ($ᵗ spec.Range i)) spec
        (simulateQ seededOracle main).run' (recorded.addValues answers)]
      · let : MeasurableSpace (List (spec.Range i)) := ⊤
        rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
        apply Measure.bind_congr_right
        apply Filter.Eventually.of_forall
        intro answers
        exact ih (recorded.addValues answers)
      · apply SeededDeferred.measure_of_compat
        exact congrArg SPMF.toMeasure
          (seededOracle.evalSPMF_liftComp_replicate_uniformSample_bind_simulateQ_run'_addValues
            i main (budget i) recorded)

/-- The same law holds after dropping the forked family's unused suffix. In
particular, a private family first visited on replay needs no eager allocation. -/
theorem generate_erased_suffix_run (main : OracleComp spec A) (budget : I → Nat)
    (families : List I) (recorded : QuerySeed spec) (target : I) :
    𝒟[do
      let suffix ← liftComp (generateSeed spec budget families) spec
      (simulateQ seededOracle main).run' (append recorded (suffix.update target []))] =
      𝒟[(simulateQ seededOracle main).run' recorded] := by
  induction families generalizing recorded with
  | nil =>
      have hempty : (∅ : QuerySeed spec).update target [] = ∅ := by
        simpa only [QuerySeed.empty_apply] using QuerySeed.update_eq_self (∅ : QuerySeed spec) target
      simp [hempty, append_empty]
  | cons i families ih =>
      simp only [generateSeed_cons, liftComp_bind, liftComp_pure, bind_assoc, pure_bind]
      let : MeasurableSpace (List (spec.Range i)) := ⊤
      by_cases h : i = target
      · subst i
        simp only [erase_prepend_self]
        trans 𝒟[do
          let _ ← liftComp (replicate (budget target) ($ᵗ spec.Range target)) spec
          (simulateQ seededOracle main).run' recorded]
        · conv_lhs => rw [evalDist_bind_of_discrete]
          conv_rhs => rw [evalDist_bind_of_discrete]
          apply Measure.bind_congr_right
          exact Filter.Eventually.of_forall (fun _ => ih recorded)
        · apply SeededDeferred.measure_of_compat
          apply congrArg SPMF.toMeasure
          apply evalSPMF_ext
          intro result
          rw [probOutput_bind_const]
          simp
      · simp only [erase_prepend_other _ target i h, append_prepend]
        trans 𝒟[do
          let answers ← liftComp (replicate (budget i) ($ᵗ spec.Range i)) spec
          (simulateQ seededOracle main).run' (recorded.addValues answers)]
        · rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete]
          apply Measure.bind_congr_right
          exact Filter.Eventually.of_forall (fun answers => ih (recorded.addValues answers))
        · apply SeededDeferred.measure_of_compat
          exact congrArg SPMF.toMeasure
            (seededOracle.evalSPMF_liftComp_replicate_uniformSample_bind_simulateQ_run'_addValues
              i main (budget i) recorded)

/-- After a valid prefix reset, every unencountered entry of the pregenerated
seed can be replaced by on-demand sampling in the second execution. -/
theorem generate_reset_run (main : OracleComp spec A) (budget : I → Nat)
    (families : List I) (log : QueryLog spec) (target : I) (slot : Nat)
    (answer : spec.Range target) (within : slot ≤ (restore log ∅ target).length) :
    𝒟[do
      let suffix ← liftComp (generateSeed spec budget families) spec
      (simulateQ seededOracle main).run'
        (((restore log suffix).takeAtIndex target slot).addValue target answer)] =
      𝒟[(simulateQ seededOracle main).run'
        (((restore log ∅).takeAtIndex target slot).addValue target answer)] := by
  have h (suffix : QuerySeed spec) :
      ((restore log suffix).takeAtIndex target slot).addValue target answer =
        append (((restore log ∅).takeAtIndex target slot).addValue target answer)
          (suffix.update target []) := by
    rw [restore_eq_append log suffix, reset_append _ _ target slot answer within]
  trans 𝒟[do
    let suffix ← liftComp (generateSeed spec budget families) spec
    (simulateQ seededOracle main).run'
      (append (((restore log ∅).takeAtIndex target slot).addValue target answer)
        (suffix.update target []))]
  · congr 1
    apply bind_congr
    intro suffix
    rw [h suffix]
  · exact generate_erased_suffix_run main budget families _ target

end Signatures.Runtime.SeededTrace
