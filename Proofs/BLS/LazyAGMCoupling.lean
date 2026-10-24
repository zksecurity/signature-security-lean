import Proofs.BLS.LazyAGMExtraction
import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-! Joint deferred sampling for the BLS AGM solvers. The entire adaptive
execution, transcript extraction, and final target lookup are interpreted under
one table. Full tables are proof artifacts, never part of the lazy solvers. -/

open OracleComp OracleSpec Model.LazyAGM MeasureTheory ProbabilityTheory

namespace BLS.LazyAGM.Reduction

variable {F M R G₁ G₂ : Type}

theorem lazyRun_eq_table [DecidableEq M] [Finite M] [SampleableType R]
    [SampleableType (M → R)] {α : Type} [MeasurableSpace α]
    (oa : OracleComp (baseSpec M R) α) :
    𝒟[(simulateQ (CoCDH.lazyCoinImpl (D := M) (R := R)) oa).run' ∅] =
      𝒟[do
        let table ← ($ᵗ (M → R) : ProbComp (M → R))
        simulateQ (CoCDH.coinTableImpl table) oa] := by
  apply evalDist_eq_of_evalSPMF_eq
  simpa only [tableExtending_empty] using CoCDH.evalSPMF_lazyCoin_eq_table oa ∅

/-- A table of independent pairs has exactly the law of two independent
tables. Keeping this joint law is necessary for the bad branch's hidden slope. -/
theorem maskTable_bind [Fintype M] [DecidableEq M] [SampleableType F]
    {α : Type} [MeasurableSpace α]
    (k : (M → F × F) → ProbComp α) :
    𝒟[do let masks ← ($ᵗ (M → F × F) : ProbComp (M → F × F)); k masks] =
      𝒟[do
        let a ← ($ᵗ (M → F) : ProbComp (M → F))
        let b ← ($ᵗ (M → F) : ProbComp (M → F))
        k (fun m => (a m, b m))] := by
  let : MeasurableSpace (M → F) := ⊤
  let : MeasurableSpace (M → F × F) := ⊤
  let pack : (M → F) × (M → F) → (M → F × F) := fun ab m => (ab.1 m, ab.2 m)
  have hpack : Function.Bijective pack := by
    constructor
    · intro ab cd h
      apply Prod.ext <;> funext m
      · exact congrArg (fun table => (table m).1) h
      · exact congrArg (fun table => (table m).2) h
    · intro masks
      exact ⟨(fun m => (masks m).1, fun m => (masks m).2), rfl⟩
  let paired : ProbComp ((M → F) × (M → F)) := do
    let a ← ($ᵗ (M → F) : ProbComp (M → F))
    let b ← ($ᵗ (M → F) : ProbComp (M → F))
    pure (a, b)
  have hd : 𝒟[pack <$> paired] = 𝒟[($ᵗ (M → F × F) : ProbComp (M → F × F))] := by
    dsimp only [paired]
    rw [evalDist_map_of_discrete, evalDist_pair,
      SampleableType.evalDist_uniformSample, SampleableType.evalDist_uniformSample,
      ← uniformOn_univ_prod]
    exact map_uniformOn_univ_of_bijective Measurable.of_discrete hpack
  have hb : 𝒟[(pack <$> paired) >>= k] =
      𝒟[($ᵗ (M → F × F) : ProbComp (M → F × F)) >>= k] := by
    rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete, hd]
  simpa only [paired, pack, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply] using hb.symm

variable [Field F] [SampleableType F] [Fintype M] [DecidableEq M]
  [AddCommGroup G₁] [Module F G₁] [MeasurableSpace F]

theorem goodReductionLazy_eq_eager (A : Adversary F M M G₁ G₂)
    (g X : G₁) (g₂ pk : G₂) :
    𝒟[goodReductionLazy A g X g₂ pk] =
      𝒟[goodReduction BLS.Proofs.indicatorWeight A g X g₂ pk] := by
  rw [goodReductionLazy, lazyRun_eq_table]
  apply congrArg evalDist
  unfold goodReduction
  apply bind_congr
  intro rho
  rw [goodProgram_table]
  simp [BLS.Proofs.indicatorWeight, baseCoeff_traceValue, traceValue_eq_mapIdx]

variable [AddCommGroup G₂] [Module F G₂]

theorem badReductionLazy_eq_eager (A : Adversary F M M G₁ G₂)
    (g X : G₁) (g₂ pk : G₂) :
    𝒟[badReductionLazy A g X g₂ pk] =
      𝒟[badReduction BLS.Proofs.indicatorWeight A g X g₂ pk] := by
  unfold badReductionLazy badReduction
  apply evalDist_bind_congr
  intro kappa
  rw [lazyRun_eq_table, maskTable_bind]
  apply congrArg evalDist
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  rw [badProgram_table]
  simp [BLS.Proofs.indicatorWeight, denominatorCoeff_traceValue,
    traceValue_fst, traceValue_snd, Finset.sum_add_distrib]

end BLS.LazyAGM.Reduction
