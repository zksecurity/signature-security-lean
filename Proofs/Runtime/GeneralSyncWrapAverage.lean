import Signatures.Model.CoCDH
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-! # Averaging over a sampled known key

A solver that first draws a uniform scalar and then runs a fixed-key solver succeeds with the
average of the fixed-key successes, hence no better than the best of them. This is how the
four synchronized PS solvers, which sample the known key, are bounded by the DLog class of the
backend: every fixed-key solver is realized within the budget, and the class bound is a supremum. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.SyncWrapGeneral

universe u

/-- A uniform bound on reachable continuation events bounds their composed event. -/
theorem evalDist_bind_apply_le_of_support
    {ι : Type u} {α β : Type} {spec : OracleSpec.{u, 0} ι}
    [∀ t, MeasurableSpace (spec.Range t)] [∀ t, DiscreteMeasurableSpace (spec.Range t)]
    [OracleSpec.IsMeasureSpec spec] [MeasurableSpace β]
    (mx : OracleComp spec α) (f : α → OracleComp spec β)
    {event : Set β} (hevent : MeasurableSet event) {r : ENNReal}
    (h : ∀ a ∈ support mx, 𝒟[f a] event ≤ r) :
    𝒟[mx >>= f] event ≤ r := by
  induction mx using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using h a (by simp)
  | query_bind t k ih =>
    rw [bind_assoc, evalDist_bind_of_discrete,
      MeasureTheory.Measure.bind_apply hevent Measurable.of_discrete.aemeasurable]
    calc
      _ ≤ ∫⁻ _u, r ∂𝒟[(query t : OracleComp spec (spec.Range t))] :=
        MeasureTheory.lintegral_mono fun u => ih u fun a ha =>
          h a (MonadAttach.mem_support_bind.mpr ⟨u, by simp, ha⟩)
      _ = r := by rw [MeasureTheory.lintegral_const, evalDist_apply_univ_eq_one, mul_one]

variable {F G₁ G₂ : Type} [Field F] [SampleableType F] [DecidableEq F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

omit [DecidableEq F] in
/-- Drawing the known key first and running the corresponding fixed-key solver succeeds no
better than the best fixed-key solver. -/
theorem dlog11Advantage_sample_le (g₁ : G₁) (g₂ : G₂)
    (solver : F → AlgebraicGroupModel.DLog11Adversary F G₁ G₂) (ε : ENNReal)
    (h : ∀ k, Model.dlog11Advantage g₁ g₂ (solver k) ≤ ε) :
    Model.dlog11Advantage g₁ g₂
      (fun g X h₂ Y => do let k ← ($ᵗ F : ProbComp F); solver k g X h₂ Y) ≤ ε := by
  unfold Model.dlog11Advantage at *
  have hswap : 𝒟[AlgebraicGroupModel.dlog11Exp g₁ g₂
      (fun g X h₂ Y => do let k ← ($ᵗ F : ProbComp F); solver k g X h₂ Y)] =
      𝒟[do let k ← ($ᵗ F : ProbComp F); AlgebraicGroupModel.dlog11Exp g₁ g₂ (solver k)] :=
    evalDist_eq_of_evalSPMF_eq _ _ (by
      simp only [AlgebraicGroupModel.dlog11Exp, bind_assoc]
      exact DeferredSampling.evalSPMF_bind_comm _ _ _)
  rw [hswap]
  exact evalDist_bind_apply_le_of_support _ _ (measurableSet_singleton true) fun k _ => h k

end Signatures.Runtime.SyncWrapGeneral
