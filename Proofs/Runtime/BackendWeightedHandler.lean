import Proofs.Runtime.BackendWeightedInterface
import Proofs.Runtime.BackendIndexedHandler
import Proofs.Runtime.BackendCallerCorrectness

/-! Native dispatch for weighted signature reductions with distinct hash-index
and signing-message types. Request retention, reply tags and branch selection
are executable code. Exact adaptive composition preserves the entire private
store and the caller's optional cutoff result. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.WeightedAGM.NativeHandler

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {iface : Interface (C := C) unifSpec}

section Group

variable {R G I S : Type} (request : C.Str R) (point : C.Str G) (index : C.Str I) (store : C.Str S)
  {tag : R × G → I} (tagCode : Q.Realizer (StepClass.HasProd.prod request point) index tag)
  (reply : Code Q unifSpec iface (StepClass.HasProd.prod request store) (StepClass.HasProd.prod point store))

/-- Retain the request across the stateful reply, then attach its exact index. -/
def group : Code Q unifSpec iface (StepClass.HasProd.prod request store)
    (StepClass.HasProd.prod index store) :=
  .seq (Language.withContext store (Q.identity request) reply)
    (.first store (.atomic (Q.compose (QP.pair (QP.snd point request) (QP.fst point request)) tagCode)))

omit QS QD in
theorem group_denote (r : R) (saved : S) :
    (group request point index store tagCode reply).denote (r, saved) =
      (fun p => (tag (r, p.1), p.2)) <$> reply.denote (r, saved) := by
  simp only [group, Language.withContext_denote, Code.denote, map_pure, bind_pure_comp, Functor.map_map]
  rfl

end Group

variable {F G₁ G₂ K M Input Output S : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (indexTy messageTy : Ty CryptoAtom)
  (bd : Boundary C (generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M))
    (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep indexTy messageTy bd)
  (sampler : BoundedSampler rep indexTy messageTy bd ports (iface := iface))
  (store : C.Str S)
  (hashReply : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty indexTy) store) (StepClass.HasProd.prod (rep.ty point₁) store))
  (signReply : Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty messageTy) store) (StepClass.HasProd.prod (rep.ty point₁) store))

def random : Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty (boundedNat randomBound)) store)
    (StepClass.HasProd.prod bd.idx store) :=
  .seq (.first store sampler.code) (.first store (.atomic ports.randomTag))

def inner : Code Q unifSpec iface
    (StepClass.HasProd.prod (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty indexTy)) store)
    (StepClass.HasProd.prod bd.idx store) :=
  .seq (.atomic (QD.distribute (rep.ty (boundedNat randomBound)) (rep.ty indexTy) store))
    (.branch (random rep indexTy messageTy bd ports sampler store) (group (rep.ty indexTy) (rep.ty point₁) bd.idx store ports.hashTag hashReply))

def dispatch : Code Q unifSpec iface (StepClass.HasProd.prod (generalPositions rep indexTy messageTy randomBound) store)
    (StepClass.HasProd.prod bd.idx store) :=
  .seq (.atomic (QD.distribute (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty indexTy))
    (rep.ty messageTy) store))
    (.branch (inner rep indexTy messageTy bd ports sampler store hashReply) (group (rep.ty messageTy) (rep.ty point₁) bd.idx store ports.signTag signReply))

def code : Code Q unifSpec iface (StepClass.HasProd.prod bd.pos store) (StepClass.HasProd.prod bd.idx store) :=
  .seq (.first store (.atomic ports.request)) (dispatch rep indexTy messageTy bd ports sampler store hashReply signReply)

noncomputable def source : QueryImpl (generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound) (StateT S ProbComp) := fun i => match i with
  | .inl (.inl n) => fun saved => (fun r => (r, saved)) <$>
      (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1)))
  | .inl (.inr m) => fun saved => hashReply.denote (m, saved)
  | .inr m => fun saved => signReply.denote (m, saved)

section Semantics

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

omit [Q.HasCategory] QP QS QD in
theorem random_denote (n : Fin (randomBound + 1)) (saved : S) :
    (random rep indexTy messageTy bd ports sampler store).denote (n, saved) =
      (fun r => (tagRandom (ι := indexTy.Value (cryptoBase F G₁ G₂ K M))
        (M := messageTy.Value (cryptoBase F G₁ G₂ K M)) (G₁ := G₁) ⟨n, r⟩, saved)) <$>
        (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1))) := by
  simp only [random, Code.denote, sampler.denote, map_pure, bind_pure_comp, Functor.map_map]

omit QS in
theorem code_denote (i : GeneralRequest (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) randomBound) (saved : S) :
    (code rep indexTy messageTy bd ports sampler store hashReply signReply).denote (i, saved) =
      (fun p => ((⟨i, p.1⟩ : GeneralIndex (indexTy.Value (cryptoBase F G₁ G₂ K M))
        (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound), p.2)) <$>
        ((source rep indexTy messageTy store hashReply signReply i).run saved) := by
  rcases i with (n | m) | m
  · simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind]
    exact random_denote rep indexTy messageTy bd ports sampler store n saved
  · simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind, source, StateT.run]
    exact group_denote (rep.ty indexTy) (rep.ty point₁) bd.idx store ports.hashTag hashReply m saved
  · simp only [code, dispatch, Code.denote, map_pure, pure_bind, source, StateT.run]
    exact group_denote (rep.ty messageTy) (rep.ty point₁) bd.idx store ports.signTag signReply m saved

variable [Zero G₁]
  [DecidableEq (indexTy.Value (cryptoBase F G₁ G₂ K M))]
  [DecidableEq (messageTy.Value (cryptoBase F G₁ G₂ K M))] (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

def executed : GeneralCaller.Handler (spec := generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound) (StateT S ProbComp) :=
  IndexedHandler.handler control queryCost (code rep indexTy messageTy bd ports sampler store hashReply signReply) defaultReply

omit QS in
theorem code_executed_run (i : GeneralRequest (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) randomBound) (saved : S) :
    (code rep indexTy messageTy bd ports sampler store hashReply signReply).run control queryCost (i, saved) =
      (fun p => (⟨(⟨i, p.1.value⟩, p.2), p.1.steps⟩ : Run (GeneralIndex (indexTy.Value (cryptoBase F G₁ G₂ K M))
        (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound × S))) <$>
        ((executed rep indexTy messageTy bd ports sampler store hashReply signReply control queryCost i).run saved) := by
  apply IndexedHandler.handler_run
  exact IndexedHandler.matches_of_denote control queryCost _ (source rep indexTy messageTy store hashReply signReply)
    (code_denote rep indexTy messageTy bd ports sampler store hashReply signReply)

omit QS in
theorem executed_erase (i : GeneralRequest (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) randomBound) (saved : S) :
    (fun p => (p.1.value, p.2)) <$>
      ((executed rep indexTy messageTy bd ports sampler store hashReply signReply control queryCost i).run saved) =
        ((source rep indexTy messageTy store hashReply signReply i).run saved) :=
  IndexedHandler.handler_erase control queryCost _ defaultReply (source rep indexTy messageTy store hashReply signReply)
    (code_denote rep indexTy messageTy bd ports sampler store hashReply signReply) i saved

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def caller (fuel : Nat) : Code Q unifSpec iface (StepClass.HasProd.prod bd.input store)
    (Caller.result (bd := bd) store) :=
  Caller.program R store (code rep indexTy messageTy bd ports sampler store hashReply signReply) fuel

omit [Zero G₁] in
theorem caller_denote (fuel : Nat) (input : Input) (saved : S) :
    (caller rep indexTy messageTy bd ports sampler store hashReply signReply R fuel).denote (input, saved) =
      (R.machine.runWithInput (source rep indexTy messageTy store hashReply signReply) fuel input).run saved :=
  Caller.program_denote R store _ (source rep indexTy messageTy store hashReply signReply) (code_denote rep indexTy messageTy bd ports sampler store hashReply signReply) fuel input saved

omit [Zero G₁] in
theorem caller_erase (fuel : Nat) (program : Input → OracleComp (generalSpec (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound) Output)
    (hprogram : R.machine.ImplementsWithin program fuel) (input : Input) (saved : S) :
    Run.value <$> (caller rep indexTy messageTy bd ports sampler store hashReply signReply R fuel).run control queryCost (input, saved) =
      (some <$> simulateQ (source rep indexTy messageTy store hashReply signReply) (program input)).run saved := by
  rw [Code.run_erase, caller_denote rep indexTy messageTy bd ports sampler store hashReply signReply R]
  rw [hprogram.simulateQ_run_eq]

end Semantics
end Signatures.Runtime.WeightedAGM.NativeHandler
