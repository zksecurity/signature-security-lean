import Proofs.Runtime.MachineSampling
import Proofs.Runtime.ProgramSimulation
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.EvalDist.AnswerMeasure

/-! The sampling-request tree has exactly the original ideal machine law.
The bridge uses the native measure semantics of `uniformSample`, not support
inclusion or a new randomness hypothesis. -/

namespace Signatures.Runtime.MachineSampling

open OracleComp OracleSpec MeasureTheory ProbabilityTheory

noncomputable abbrev uniformNaturals : QueryImpl unifSpec PMF :=
  fun n => Signatures.Runtime.RejectionSampling.uniformOfFintype (Fin (n+1))

/-- The uniform answer measure of one selection query is the uniform `PMF` as a measure. -/
private theorem uniform_bind_toMeasure {A : Type} [MeasurableSpace A] (n : Nat)
    (k : Fin (n + 1) → PMF A) :
    @Measure.bind _ _ ⊤ _ (@uniformOn (Fin (n + 1)) ⊤ Set.univ) (fun b => (k b).toMeasure) =
      ((Signatures.Runtime.RejectionSampling.uniformOfFintype (Fin (n + 1))).bind k).toMeasure := by
  let : MeasurableSpace (Fin (n + 1)) := ⊤
  ext s hs
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable, lintegral_countable',
    PMF.toMeasure_bind_apply _ _ _ hs]
  exact tsum_congr fun b => by
    rw [mul_comm, uniformOn_univ_apply_singleton,
      Signatures.Runtime.RejectionSampling.uniformOfFintype_apply]

theorem ideal_measure {A : Type} [MeasurableSpace A] (code : ProbComp A) :
    𝒟[code] = (simulateQ uniformNaturals code).toMeasure := by
  induction code using OracleComp.inductionOn with
  | pure a =>
    rw [simulateQ_pure, evalDist_pure]
    exact Eq.symm (PMF.toMeasure_pure a)
  | query_bind n k ih =>
    let : MeasurableSpace (Fin (n + 1)) := ⊤
    rw [evalDist_bind_of_discrete, simulateQ_query_bind, funext ih,
      evalDist_liftM_unifSpec_query]
    exact uniform_bind_toMeasure n _

theorem uniformSample_law (A : Type) [SampleableType A] [Fintype A] :
    simulateQ uniformNaturals (uniformSample A) = Signatures.Runtime.RejectionSampling.uniformOfFintype A := by
  let : MeasurableSpace A := ⊤
  ext a
  have h := congrArg (fun μ : Measure A => μ {a}) (ideal_measure (uniformSample A))
  rw [SampleableType.evalDist_uniformSample, uniformOn_univ_apply_singleton,
    PMF.toMeasure_apply_singleton _ a (MeasurableSet.singleton a)] at h
  simpa only [Signatures.Runtime.RejectionSampling.uniformOfFintype_apply] using h.symm

variable {r : Nat} [Fact r.Prime] [SampleableType (ZMod r)] {G₁ G₂ K M : Type}

theorem effects_ideal_probability (sampling : Machine.SamplingCosts) (storage : Ty CryptoAtom)
    {a b} (cmd : Machine.Effect storage a b) (arg : a.Value (cryptoBase (ZMod r) G₁ G₂ K M)) :
    StateT.mapHom (simulateQ' (ideal r)) (effects (ZMod r) G₁ G₂ K M sampling storage cmd arg) =
      StateT.mapHom (simulateQ' uniformNaturals) (Machine.effects sampling storage cmd arg) := by
  funext state
  cases cmd <;> simp [StateT.mapHom, StateT.mk, StateT.run, effects, Machine.effects, ideal,
    uniformSample_law, uniformNaturals]

variable [DecidableEq K] [DecidableEq M] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module (ZMod r) G₁] [AddCommGroup G₂] [Module (ZMod r) G₂]

theorem tree_ideal_probability (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (code : Machine.Code Γ a) (env : Env (cryptoBase (ZMod r) G₁ G₂ K M) Γ) :
    simulateQ (ideal r) (tree cost sampling code env) =
      simulateQ uniformNaturals (code.run cost sampling env) := by
  have h := code.body.run_mmap (StateT.mapHom (simulateQ' (ideal r)))
    (arithmetic (ZMod r) G₁ G₂ K M cost) (effects (ZMod r) G₁ G₂ K M sampling code.store) env
  simp_rw [effects_ideal_probability sampling code.store] at h
  rw [← code.body.run_mmap (StateT.mapHom (simulateQ' uniformNaturals))] at h
  have h := congrArg (fun x => x.run (code.init.run (arithmetic (ZMod r) G₁ G₂ K M cost) env).value) h
  simp only [StateT.run_mapHom] at h
  simp only [tree, Machine.Code.run, simulateQ_bind, simulateQ_pure, h]

theorem package_ideal_probability (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    {Γ a} (pack : Machine.Package (cryptoBase (ZMod r) G₁ G₂ K M) Γ a)
    (env : Env (cryptoBase (ZMod r) G₁ G₂ K M) Γ) :
    simulateQ (ideal r) (packageTree cost sampling pack env) =
      simulateQ uniformNaturals (pack.run cost sampling env) := by
  simp only [packageTree, Machine.Package.run_eq, simulateQ_map, tree_ideal_probability]

end Signatures.Runtime.MachineSampling
