import Signatures.Runtime.BackendSignatureHandler
import Signatures.Runtime.BackendLazyAGMSimulation

/-! Both lazy BLS AGM replies installed in the common native dispatcher. The
source refinement retains the fixed challenge configuration, private list cache,
and every chronological reply token across arbitrary adaptive callers. -/

open OracleComp OracleSpec PFunctor Model.LazyAGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.LazyAGM.NativeHandler

open BackendProgram Coron

set_option backward.isDefEq.respectTransparency false

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ M Input Output : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)

abbrev goodCode := SignatureHandler.code rep bd ports sampler (rep.ty (storeTy scalar goodConfigTy))
  (backendGoodReply rep data cost primitive sampling)

abbrev badCode := SignatureHandler.code rep bd ports sampler (rep.ty (storeTy (.pair scalar scalar) badConfigTy))
  (backendBadReply rep data cost primitive sampling)

noncomputable abbrev goodSource := SignatureHandler.source rep (rep.ty (storeTy scalar goodConfigTy))
  (backendGoodReply rep data cost primitive sampling) (randomBound := randomBound)

noncomputable abbrev badSource := SignatureHandler.source rep (rep.ty (storeTy (.pair scalar scalar) badConfigTy))
  (backendBadReply rep data cost primitive sampling) (randomBound := randomBound)

omit QD in
theorem goodSource_refines (g X : G₁) (i : GeneralRequest M randomBound) :
    StateRefines (fun state : State M F G₁ => ((g, X), state))
      (simulateQ (listOracle (fun rho : F => rho • g) (fun rho => rho • X)) (generalSource randomBound i))
      (goodSource rep data cost primitive sampling i) := by
  intro state
  rcases state with ⟨cache, tr⟩
  rcases i with (n | m) | m
  · simp only [generalSource, simulateQ_spec_query, listOracle, SignatureHandler.source,
      StateT.run, Functor.map_map]
    rfl
  · simp only [generalSource, simulateQ_spec_query, listOracle, listReply,
      SignatureHandler.source, StateT.run, Functor.map_map]
    rw [backendGoodReply_denote]
    rfl
  · simp only [generalSource, simulateQ_spec_query, listOracle, listReply,
      SignatureHandler.source, StateT.run, Functor.map_map]
    rw [backendGoodReply_denote]
    rfl

omit QD in
theorem badSource_refines (g X : G₁) (kappa : F) (i : GeneralRequest M randomBound) :
    StateRefines (fun state : State M (F × F) G₁ => ((kappa, g, X), state))
      (simulateQ (listOracle (fun masks : F × F => masks.1 • X + masks.2 • g)
        (fun masks => kappa • (masks.1 • X + masks.2 • g))) (generalSource randomBound i))
      (badSource rep data cost primitive sampling i) := by
  intro state
  rcases state with ⟨cache, tr⟩
  rcases i with (n | m) | m
  · simp only [generalSource, simulateQ_spec_query, listOracle, SignatureHandler.source,
      StateT.run, Functor.map_map]
    rfl
  · simp only [generalSource, simulateQ_spec_query, listOracle, listReply,
      SignatureHandler.source, StateT.run, Functor.map_map]
    rw [backendBadReply_denote]
    rfl
  · simp only [generalSource, simulateQ_spec_query, listOracle, listReply,
      SignatureHandler.source, StateT.run, Functor.map_map]
    rw [backendBadReply_denote]
    rfl

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

abbrev goodCaller (fuel : Nat) := SignatureHandler.caller rep bd ports sampler (rep.ty (storeTy scalar goodConfigTy))
  (backendGoodReply rep data cost primitive sampling) R fuel

abbrev badCaller (fuel : Nat) := SignatureHandler.caller rep bd ports sampler (rep.ty (storeTy (.pair scalar scalar) badConfigTy))
  (backendBadReply rep data cost primitive sampling) R fuel

theorem goodCaller_source (fuel : Nat) (program : Input → OracleComp (generalSpec M G₁ randomBound) Output)
    (hprogram : R.machine.ImplementsWithin program fuel) (input : Input)
    (g X : G₁) (state : State M F G₁) :
    (goodCaller rep bd ports sampler data cost primitive sampling R fuel).denote (input, (g, X), state) =
      (fun p => (some p.1, (g, X), p.2)) <$>
        (simulateQ (listOracle (fun rho : F => rho • g) (fun rho => rho • X))
          (simulateQ (generalSource randomBound) (program input))).run state := by
  rw [SignatureHandler.caller_denote, hprogram.simulateQ_run_eq]
  have h := GeneralCaller.simulateQ_refines (fun s : State M F G₁ => ((g, X), s))
    (fun i => simulateQ (listOracle (fun rho : F => rho • g) (fun rho => rho • X)) (generalSource randomBound i))
    (goodSource rep data cost primitive sampling)
    (goodSource_refines rep data cost primitive sampling g X) (program input) state
  change _ = (simulateQ (goodSource rep data cost primitive sampling) (program input)).run ((g, X), state) at h
  simp only [StateT.run_map]
  rw [← h]
  simp only [Functor.map_map]
  rw [← QueryImpl.simulateQ_compose]
  rfl

theorem badCaller_source (fuel : Nat) (program : Input → OracleComp (generalSpec M G₁ randomBound) Output)
    (hprogram : R.machine.ImplementsWithin program fuel) (input : Input)
    (g X : G₁) (kappa : F) (state : State M (F × F) G₁) :
    (badCaller rep bd ports sampler data cost primitive sampling R fuel).denote (input, (kappa, g, X), state) =
      (fun p => (some p.1, (kappa, g, X), p.2)) <$>
        (simulateQ (listOracle (fun masks : F × F => masks.1 • X + masks.2 • g)
          (fun masks => kappa • (masks.1 • X + masks.2 • g)))
          (simulateQ (generalSource randomBound) (program input))).run state := by
  rw [SignatureHandler.caller_denote, hprogram.simulateQ_run_eq]
  have h := GeneralCaller.simulateQ_refines (fun s : State M (F × F) G₁ => ((kappa, g, X), s))
    (fun i => simulateQ (listOracle (fun masks : F × F => masks.1 • X + masks.2 • g)
      (fun masks => kappa • (masks.1 • X + masks.2 • g))) (generalSource randomBound i))
    (badSource rep data cost primitive sampling)
    (badSource_refines rep data cost primitive sampling g X kappa) (program input) state
  change _ = (simulateQ (badSource rep data cost primitive sampling) (program input)).run ((kappa, g, X), state) at h
  simp only [StateT.run_map]
  rw [← h]
  simp only [Functor.map_map]
  rw [← QueryImpl.simulateQ_compose]
  rfl

end Signatures.Runtime.LazyAGM.NativeHandler
