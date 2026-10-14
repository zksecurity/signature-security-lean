import Signatures.Runtime.BackendWeightedHandler
import Signatures.Runtime.BackendWeightedReplySemantics
import Signatures.Runtime.WeightedExecution
import Signatures.Runtime.GeneralCallerRefinement

/-! Install the actual weighted reply programs in the native dispatcher. Both
branches preserve the fixed challenge, finite cache, and explicit reply logs
across every adaptive general caller. Complete runtime composition is separate. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeHandler

open BackendProgram Reply

set_option backward.isDefEq.respectTransparency false

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

abbrev goodCode := code rep index.ty index.messageTy bd ports sampler (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))
  (goodHash rep data cost primitive sampling index) (goodSign rep data cost primitive sampling index)

abbrev badCode := code rep index.ty index.messageTy bd ports sampler (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))
  (badHash rep data cost primitive sampling index) (badSign rep data cost primitive sampling index)

noncomputable abbrev goodSource := source rep index.ty index.messageTy (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))
  (goodHash rep data cost primitive sampling index) (goodSign rep data cost primitive sampling index) (randomBound := randomBound)

noncomputable abbrev badSource := source rep index.ty index.messageTy (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))
  (badHash rep data cost primitive sampling index) (badSign rep data cost primitive sampling index) (randomBound := randomBound)

omit QD in
theorem goodSource_refines (g X : G₁) (i : GeneralRequest (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) randomBound) :
    StateRefines (fun state : State (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) F G₁ => ((g, X), state))
      (simulateQ (listOracle (index.sourceTerms cost) (fun rho : F => rho • g) (fun rho => rho • X)) (generalSource randomBound i))
      (goodSource rep index data cost primitive sampling i) := by
  intro state
  rcases state with ⟨cache, tr⟩
  rcases i with (n | m) | m
  · simp only [generalSource, simulateQ_spec_query, listOracle, source,
      StateT.run, Functor.map_map]
    rfl
  · simp only [generalSource, simulateQ_spec_query, listOracle, listReply,
      source, StateT.run, Functor.map_map]
    rw [goodHash_denote]
    rfl
  · simp only [generalSource, simulateQ_spec_query, listOracle, listReply,
      source, StateT.run, Functor.map_map]
    rw [goodSign_denote]
    rfl

omit QD in
theorem badSource_refines (g X : G₁) (kappa : F) (i : GeneralRequest (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) randomBound) :
    StateRefines (fun state : State (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) (F × F) G₁ => ((kappa, g, X), state))
      (simulateQ (listOracle (index.sourceTerms cost) (fun masks : F × F => masks.1 • X + masks.2 • g)
        (fun masks => kappa • (masks.1 • X + masks.2 • g))) (generalSource randomBound i))
      (badSource rep index data cost primitive sampling i) := by
  intro state
  rcases state with ⟨cache, tr⟩
  rcases i with (n | m) | m
  · simp only [generalSource, simulateQ_spec_query, listOracle, source,
      StateT.run, Functor.map_map]
    rfl
  · simp only [generalSource, simulateQ_spec_query, listOracle, listReply,
      source, StateT.run, Functor.map_map]
    rw [badHash_denote]
    rfl
  · simp only [generalSource, simulateQ_spec_query, listOracle, listReply,
      source, StateT.run, Functor.map_map]
    rw [badSign_denote]
    rfl

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

abbrev goodCaller (fuel : Nat) := caller rep index.ty index.messageTy bd ports sampler (rep.ty (storeTy index.ty index.messageTy scalar LazyAGM.goodConfigTy))
  (goodHash rep data cost primitive sampling index) (goodSign rep data cost primitive sampling index) R fuel

abbrev badCaller (fuel : Nat) := caller rep index.ty index.messageTy bd ports sampler (rep.ty (storeTy index.ty index.messageTy (.pair scalar scalar) LazyAGM.badConfigTy))
  (badHash rep data cost primitive sampling index) (badSign rep data cost primitive sampling index) R fuel

theorem goodCaller_source (fuel : Nat) (program : Input → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound) Output)
    (hprogram : R.machine.ImplementsWithin program fuel) (input : Input)
    (g X : G₁) (state : State (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) F G₁) :
    (goodCaller rep index bd ports sampler data cost primitive sampling R fuel).denote (input, (g, X), state) =
      (fun p => (some p.1, (g, X), p.2)) <$>
        (simulateQ (listOracle (index.sourceTerms cost) (fun rho : F => rho • g) (fun rho => rho • X))
          (simulateQ (generalSource randomBound) (program input))).run state := by
  rw [caller_denote, hprogram.simulateQ_run_eq]
  have h := GeneralCaller.simulateQ_refines (fun s : State (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) F G₁ => ((g, X), s))
    (fun i => simulateQ (listOracle (index.sourceTerms cost) (fun rho : F => rho • g) (fun rho => rho • X)) (generalSource randomBound i))
    (goodSource rep index data cost primitive sampling)
    (goodSource_refines rep index data cost primitive sampling g X) (program input) state
  change _ = (simulateQ (goodSource rep index data cost primitive sampling) (program input)).run ((g, X), state) at h
  simp only [StateT.run_map]
  rw [← h]
  simp only [Functor.map_map]
  rw [← QueryImpl.simulateQ_compose]
  rfl

theorem badCaller_source (fuel : Nat) (program : Input → OracleComp (generalSpec (index.ty.Value (cryptoBase F G₁ G₂ K M))
    (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound) Output)
    (hprogram : R.machine.ImplementsWithin program fuel) (input : Input)
    (g X : G₁) (kappa : F) (state : State (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) (F × F) G₁) :
    (badCaller rep index bd ports sampler data cost primitive sampling R fuel).denote (input, (kappa, g, X), state) =
      (fun p => (some p.1, (kappa, g, X), p.2)) <$>
        (simulateQ (listOracle (index.sourceTerms cost) (fun masks : F × F => masks.1 • X + masks.2 • g)
          (fun masks => kappa • (masks.1 • X + masks.2 • g)))
          (simulateQ (generalSource randomBound) (program input))).run state := by
  rw [caller_denote, hprogram.simulateQ_run_eq]
  have h := GeneralCaller.simulateQ_refines (fun s : State (index.ty.Value (cryptoBase F G₁ G₂ K M)) (index.messageTy.Value (cryptoBase F G₁ G₂ K M)) (F × F) G₁ => ((kappa, g, X), s))
    (fun i => simulateQ (listOracle (index.sourceTerms cost) (fun masks : F × F => masks.1 • X + masks.2 • g)
      (fun masks => kappa • (masks.1 • X + masks.2 • g))) (generalSource randomBound i))
    (badSource rep index data cost primitive sampling)
    (badSource_refines rep index data cost primitive sampling g X kappa) (program input) state
  change _ = (simulateQ (badSource rep index data cost primitive sampling) (program input)).run ((kappa, g, X), state) at h
  simp only [StateT.run_map]
  rw [← h]
  simp only [Functor.map_map]
  rw [← QueryImpl.simulateQ_compose]
  rfl

end Signatures.Runtime.WeightedAGM.NativeHandler
