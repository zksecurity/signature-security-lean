import Proofs.Runtime.BackendWeightedOracle
import Proofs.Runtime.BackendWeightedCallerOutput
import Proofs.Runtime.WeightedExecutionCache

/-! The actual weighted native interaction supplies the cached-transcript
invariant needed by extraction. General attacker resources give enough fuel;
exact source correspondence then transfers cache preservation to every supported
native run. No arithmetic attacker syntax or caller-specific invariant is used. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM Model.LazyAGM.WeightedReduction
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeHandler

open BackendProgram Reply

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M Input Output : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (index : Index)
  (bd : Boundary C (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep index.ty index.messageTy bd) (sampler : BoundedSampler rep index.ty index.messageTy bd ports (iface := iface))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

variable (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

include hrun

theorem goodCaller_cached_of_resources
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound) Output)
    (hprogram : R.machine.Implements program) (input : Input) (g X : G₁)
    (state : State (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) F G₁)
    (hc : TranscriptCached (index.sourceTerms cost) (chronological state.2) state.1)
    (z : Run (Option Output × (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support ((goodCaller rep index bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, (g, X), state))) :
    (∃ output, z.value.1 = some output) ∧ z.value.2.1 = (g, X) ∧
      CacheExtends state.1 z.value.2.2.1 ∧
      TranscriptCached (index.sourceTerms cost) (chronological z.value.2.2.2) z.value.2.2.1 := by
  have hv := Code.value_mem_denote control queryCost
    (goodCaller rep index bd ports sampler data cost primitive sampling R fuel) (input, (g, X), state) z hz
  rw [goodCaller_source rep index bd ports sampler data cost primitive sampling R fuel program
    (GeneralCaller.implementsWithin_of_resources R bound hrun program hprogram fuel hfuel), support_map] at hv
  obtain ⟨p, hp, he⟩ := hv
  have hs := listSimulation_cached (index.sourceTerms cost) (fun rho : F => rho • g) (fun rho => rho • X)
    (simulateQ (generalSource randomBound) (program input)) state hc p hp
  rw [← he]
  exact ⟨⟨p.1, rfl⟩, rfl, hs⟩

theorem badCaller_cached_of_resources
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound) Output)
    (hprogram : R.machine.Implements program) (input : Input) (g X : G₁) (kappa : F)
    (state : State (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) (F × F) G₁)
    (hc : TranscriptCached (index.sourceTerms cost) (chronological state.2) state.1)
    (z : Run (Option Output × (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support ((badCaller rep index bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, (kappa, g, X), state))) :
    (∃ output, z.value.1 = some output) ∧ z.value.2.1 = (kappa, g, X) ∧
      CacheExtends state.1 z.value.2.2.1 ∧
      TranscriptCached (index.sourceTerms cost) (chronological z.value.2.2.2) z.value.2.2.1 := by
  have hv := Code.value_mem_denote control queryCost
    (badCaller rep index bd ports sampler data cost primitive sampling R fuel) (input, (kappa, g, X), state) z hz
  rw [badCaller_source rep index bd ports sampler data cost primitive sampling R fuel program
    (GeneralCaller.implementsWithin_of_resources R bound hrun program hprogram fuel hfuel), support_map] at hv
  obtain ⟨p, hp, he⟩ := hv
  have hs := listSimulation_cached (index.sourceTerms cost) (fun masks : F × F => masks.1 • X + masks.2 • g)
      (fun masks => kappa • (masks.1 • X + masks.2 • g))
    (simulateQ (generalSource randomBound) (program input)) state hc p hp
  rw [← he]
  exact ⟨⟨p.1, rfl⟩, rfl, hs⟩

theorem goodCaller_cached_from_empty
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound) Output)
    (hprogram : R.machine.Implements program) (input : Input) (g X : G₁)
    (z : Run (Option Output × (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support ((goodCaller rep index bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, (g, X), [], ([], [])))) :
    (∃ output, z.value.1 = some output) ∧ z.value.2.1 = (g, X) ∧
      TranscriptCached (index.sourceTerms cost) (chronological z.value.2.2.2) z.value.2.2.1 := by
  have h := goodCaller_cached_of_resources rep index bd ports sampler data cost primitive sampling
    R bound hrun control queryCost fuel hfuel program hprogram input g X ([], ([], []))
    (by simp [TranscriptCached, chronological]) z hz
  exact ⟨h.1, h.2.1, h.2.2.2⟩

theorem badCaller_cached_from_empty
    (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
      (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound) Output)
    (hprogram : R.machine.Implements program) (input : Input) (g X : G₁) (kappa : F)
    (z : Run (Option Output × (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy).Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support ((badCaller rep index bd ports sampler data cost primitive sampling R fuel).run
      control queryCost (input, (kappa, g, X), [], ([], [])))) :
    (∃ output, z.value.1 = some output) ∧ z.value.2.1 = (kappa, g, X) ∧
      TranscriptCached (index.sourceTerms cost) (chronological z.value.2.2.2) z.value.2.2.1 := by
  have h := badCaller_cached_of_resources rep index bd ports sampler data cost primitive sampling
    R bound hrun control queryCost fuel hfuel program hprogram input g X kappa ([], ([], []))
    (by simp [TranscriptCached, chronological]) z hz
  exact ⟨h.1, h.2.1, h.2.2.2⟩

end Signatures.Runtime.WeightedAGM.NativeHandler
