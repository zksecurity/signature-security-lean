import Signatures.Runtime.BackendCoronInterface
import Signatures.Runtime.BackendIndexedHandler
import Signatures.Runtime.BackendCallerCorrectness

/-! Native random/hash/sign dispatch shared by signature reductions. The caller
input/output and private store are arbitrary represented types. Hash/sign code
is instantiated by each reduction; all request decoding, request retention,
response tagging, and branch selection are executable backend code. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SignatureHandler

open BackendProgram Coron

def defaultReply {M G₁ : Type} [Zero G₁] {randomBound : Nat} :
    (i : GeneralRequest M randomBound) → (generalSpec M G₁ randomBound).Range i
  | .inl (.inl n) => (0 : Fin (n.val + 1))
  | .inl (.inr _) => (0 : G₁)
  | .inr _ => (0 : G₁)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ M Input Output S : Type} {randomBound : Nat}
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (store : C.Str S)
  (reply : (signing : Bool) → Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty message) store) (StepClass.HasProd.prod (rep.ty point₁) store))

def group (signing : Bool) :
    Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty message) store)
      (StepClass.HasProd.prod bd.idx store) :=
  .seq (Language.withContext store (Q.identity (rep.ty message)) (reply signing))
    (.first store (.atomic (Q.compose
      (QP.pair (QP.snd (rep.ty point₁) (rep.ty message)) (QP.fst (rep.ty point₁) (rep.ty message)))
      (ports.groupTag signing))))

def random : Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty (boundedNat randomBound)) store)
    (StepClass.HasProd.prod bd.idx store) :=
  .seq (.first store sampler.code) (.first store (.atomic ports.randomTag))

def inner : Code Q unifSpec iface
    (StepClass.HasProd.prod (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message)) store)
    (StepClass.HasProd.prod bd.idx store) :=
  .seq (.atomic (QD.distribute (rep.ty (boundedNat randomBound)) (rep.ty message) store))
    (.branch (random rep bd ports sampler store) (group rep bd ports store reply false))

def dispatch : Code Q unifSpec iface (StepClass.HasProd.prod (generalPositions rep randomBound) store)
    (StepClass.HasProd.prod bd.idx store) :=
  .seq (.atomic (QD.distribute (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message))
    (rep.ty message) store))
    (.branch (inner rep bd ports sampler store reply) (group rep bd ports store reply true))

def code : Code Q unifSpec iface (StepClass.HasProd.prod bd.pos store) (StepClass.HasProd.prod bd.idx store) :=
  .seq (.first store (.atomic ports.request)) (dispatch rep bd ports sampler store reply)

noncomputable def source : QueryImpl (generalSpec M G₁ randomBound) (StateT S ProbComp) := fun i => match i with
  | .inl (.inl n) => fun saved => (fun r => (r, saved)) <$>
      (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1)))
  | .inl (.inr m) => fun saved => (reply false).denote (m, saved)
  | .inr m => fun saved => (reply true).denote (m, saved)

section Semantics

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

omit QS QD in
theorem group_denote (signing : Bool) (m : M) (saved : S) :
    (group rep bd ports store reply signing).denote (m, saved) =
      (fun p => (tagGroup (G₁ := G₁) signing (m, p.1), p.2)) <$> (reply signing).denote (m, saved) := by
  simp only [group, Language.withContext_denote, Code.denote, map_pure, bind_pure_comp, Functor.map_map]
  rfl

omit [Q.HasCategory] QP QS QD in
theorem random_denote (n : Fin (randomBound + 1)) (saved : S) :
    (random rep bd ports sampler store).denote (n, saved) =
      (fun r => (tagRandom (M := M) (G₁ := G₁) ⟨n, r⟩, saved)) <$>
        (liftM (unifSpec.query n.val) : ProbComp (Fin (n.val + 1))) := by
  simp only [random, Code.denote, sampler.denote, map_pure, bind_pure_comp, Functor.map_map]

omit QS in
theorem code_denote (i : GeneralRequest M randomBound) (saved : S) :
    (code rep bd ports sampler store reply).denote (i, saved) =
      (fun p => ((⟨i, p.1⟩ : GeneralIndex M G₁ randomBound), p.2)) <$>
        ((source rep store reply i).run saved) := by
  rcases i with (n | m) | m
  · simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind]
    exact random_denote rep bd ports sampler store n saved
  · simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind, source, StateT.run]
    exact group_denote rep bd ports store reply false m saved
  · simp only [code, dispatch, Code.denote, map_pure, pure_bind, source, StateT.run]
    exact group_denote rep bd ports store reply true m saved

variable [Zero G₁] [DecidableEq M] (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

def executed : GeneralCaller.Handler (spec := generalSpec M G₁ randomBound) (StateT S ProbComp) :=
  IndexedHandler.handler control queryCost (code rep bd ports sampler store reply) defaultReply

omit QS in
theorem code_executed_run (i : GeneralRequest M randomBound) (saved : S) :
    (code rep bd ports sampler store reply).run control queryCost (i, saved) =
      (fun p => (⟨(⟨i, p.1.value⟩, p.2), p.1.steps⟩ : Run (GeneralIndex M G₁ randomBound × S))) <$>
        ((executed rep bd ports sampler store reply control queryCost i).run saved) := by
  apply IndexedHandler.handler_run
  exact IndexedHandler.matches_of_denote control queryCost _ (source rep store reply)
    (code_denote rep bd ports sampler store reply)

omit QS in
theorem executed_erase (i : GeneralRequest M randomBound) (saved : S) :
    (fun p => (p.1.value, p.2)) <$>
      ((executed rep bd ports sampler store reply control queryCost i).run saved) =
        ((source rep store reply i).run saved) :=
  IndexedHandler.handler_erase control queryCost _ defaultReply (source rep store reply)
    (code_denote rep bd ports sampler store reply) i saved

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def caller (fuel : Nat) : Code Q unifSpec iface (StepClass.HasProd.prod bd.input store)
    (Caller.result (bd := bd) store) :=
  Caller.program R store (code rep bd ports sampler store reply) fuel

omit [Zero G₁] in
theorem caller_denote (fuel : Nat) (input : Input) (saved : S) :
    (caller rep bd ports sampler store reply R fuel).denote (input, saved) =
      (R.machine.runWithInput (source rep store reply) fuel input).run saved :=
  Caller.program_denote R store _ (source rep store reply) (code_denote rep bd ports sampler store reply) fuel input saved

omit [Zero G₁] in
theorem caller_erase (fuel : Nat) (program : Input → OracleComp (generalSpec M G₁ randomBound) Output)
    (hprogram : R.machine.ImplementsWithin program fuel) (input : Input) (saved : S) :
    Run.value <$> (caller rep bd ports sampler store reply R fuel).run control queryCost (input, saved) =
      (some <$> simulateQ (source rep store reply) (program input)).run saved := by
  rw [Code.run_erase, caller_denote rep bd ports sampler store reply R]
  rw [hprogram.simulateQ_run_eq]

end Semantics
end Signatures.Runtime.SignatureHandler
