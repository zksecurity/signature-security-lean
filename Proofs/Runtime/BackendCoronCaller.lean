import Proofs.Runtime.BackendCoronHandler
import Proofs.Runtime.BackendIndexedHandler
import Proofs.Runtime.BackendCallerCorrectness

/-! Assemble a general caller with the constructed Coron dispatcher. Its costed
handler is a typed view of actual native execution, with exactly the same work.
The assembly preserves adaptive source semantics and the final store. This is
the stateful caller phase; challenge initialization and final extraction must
still be composed and the full solver resource bound derived. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Coron.NativeHandler

open BackendProgram

def defaultReply {M G₁ : Type} [Zero G₁] {randomBound : Nat} :
    (i : GeneralRequest M randomBound) → (generalSpec M G₁ randomBound).Range i
  | .inl (.inl n) => (0 : Fin (n.val + 1))
  | .inl (.inr _) => (0 : G₁)
  | .inr _ => (0 : G₁)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor G₂ (M × G₁))
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (data : DataCode Q rep.data) (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

def executed (qS : Nat) : GeneralCaller.Handler (spec := generalSpec M G₁ randomBound)
    (StateT ((machineStore qS).Value (cryptoBase F G₁ G₂ M M)) ProbComp) :=
  IndexedHandler.handler control queryCost (code rep bd ports sampler data samplingCode cost primitive qS) defaultReply

noncomputable def sourceHandler (sampling : Machine.SamplingCosts) (qS : Nat) :
    QueryImpl (generalSpec M G₁ randomBound) (StateT ((machineStore qS).Value (cryptoBase F G₁ G₂ M M)) ProbComp) :=
  fun i => Run.value <$> generalHandler (F := F) (G₂ := G₂) cost sampling qS randomBound i

section Semantics

attribute [local implicit_reducible] PFunctor.Idx
set_option backward.isDefEq.respectTransparency false

omit [C.HasOption] in
theorem code_sourceHandler (sampling : Machine.SamplingCosts) (qS : Nat) (i : GeneralRequest M randomBound)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (code rep bd ports sampler data samplingCode cost primitive qS).denote (i, saved) =
      (fun p => (⟨i, p.1⟩, p.2)) <$> ((sourceHandler (F := F) (G₂ := G₂) cost sampling qS i).run saved) := by
  simpa only [sourceHandler, StateT.run_map, Functor.map_map, Prod.map] using
    code_denote rep bd ports sampler data samplingCode cost primitive sampling qS i saved

omit [C.HasOption] in
theorem code_executed_run (qS : Nat) (i : GeneralRequest M randomBound)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (code rep bd ports sampler data samplingCode cost primitive qS).run control queryCost (i, saved) =
      (fun p => (⟨(⟨i, p.1.value⟩, p.2), p.1.steps⟩ : Run (GeneralIndex M G₁ randomBound ×
        (machineStore qS).Value (cryptoBase F G₁ G₂ M M)))) <$>
      ((executed rep bd ports sampler data samplingCode cost primitive control queryCost qS i).run saved) := by
  apply IndexedHandler.handler_run
  exact IndexedHandler.matches_of_denote control queryCost _
    (sourceHandler (F := F) (G₂ := G₂) cost ⟨0, fun _ => 0⟩ qS)
    (code_sourceHandler rep bd ports sampler data samplingCode cost primitive ⟨0, fun _ => 0⟩ qS)

omit [C.HasOption] in
theorem executed_erase (sampling : Machine.SamplingCosts) (qS : Nat) (i : GeneralRequest M randomBound)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (fun p => (p.1.value, p.2)) <$>
      ((executed rep bd ports sampler data samplingCode cost primitive control queryCost qS i).run saved) =
        ((sourceHandler (F := F) (G₂ := G₂) cost sampling qS i).run saved) := by
  exact IndexedHandler.handler_erase control queryCost _ defaultReply
    (sourceHandler (F := F) (G₂ := G₂) cost sampling qS)
    (code_sourceHandler rep bd ports sampler data samplingCode cost primitive sampling qS) i saved

variable [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def caller (qS fuel : Nat) : Code Q unifSpec iface
    (StepClass.HasProd.prod bd.input (rep.ty (machineStore qS)))
    (Caller.result (bd := bd) (rep.ty (machineStore qS))) :=
  Caller.program R (rep.ty (machineStore qS)) (code rep bd ports sampler data samplingCode cost primitive qS) fuel

theorem caller_denote (sampling : Machine.SamplingCosts) (qS fuel : Nat) (pk : G₂)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    (caller rep bd ports sampler data samplingCode cost primitive R qS fuel).denote (pk, saved) =
      (R.machine.runWithInput (sourceHandler (F := F) (G₂ := G₂) cost sampling qS) fuel pk).run saved := by
  exact Caller.program_denote R (rep.ty (machineStore qS)) _
    (sourceHandler (F := F) (G₂ := G₂) cost sampling qS)
    (code_sourceHandler rep bd ports sampler data samplingCode cost primitive sampling qS) fuel pk saved

theorem caller_erase (sampling : Machine.SamplingCosts) (qS fuel : Nat)
    (program : G₂ → OracleComp (generalSpec M G₁ randomBound) (M × G₁))
    (hprogram : R.machine.ImplementsWithin program fuel) (pk : G₂)
    (saved : (machineStore qS).Value (cryptoBase F G₁ G₂ M M)) :
    Run.value <$> (caller rep bd ports sampler data samplingCode cost primitive R qS fuel).run control queryCost (pk, saved) =
      (some <$> simulateQ (sourceHandler (F := F) (G₂ := G₂) cost sampling qS) (program pk)).run saved := by
  rw [Code.run_erase, caller_denote rep bd ports sampler data samplingCode cost primitive R sampling]
  rw [hprogram.simulateQ_run_eq]

end Semantics
end Signatures.Runtime.Coron.NativeHandler
