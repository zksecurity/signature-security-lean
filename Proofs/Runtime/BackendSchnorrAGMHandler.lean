import Proofs.Runtime.BackendSchnorrAGMHandlerComponents
import Proofs.Runtime.BackendIndexedHandler
import Proofs.Runtime.BackendCallerCorrectness

/-! Executable dispatch for general Schnorr AGM callers. The original request
is retained through each component call and supplied to the actual reply tagger.
The indexed-handler view is only a proof factorization of this executed code. -/

open OracleComp OracleSpec PFunctor AlgebraicGroupModel.Interaction Schnorr.AGM
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M Input Output : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

def random : Code Q unifSpec iface (rep.ty (HandlerComponents.argsStoreTy randomArgsTy))
    (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (Language.withContext (rep.ty storeTy) (Q.identity (rep.ty randomArgsTy))
    (HandlerComponents.random rep data cost primitive randomPorts))
    (.first (rep.ty storeTy) (.atomic (Q.compose
      (QP.pair (QP.snd (rep.ty (groupReplyTy .nat)) (rep.ty randomArgsTy))
        (QP.fst (rep.ty (groupReplyTy .nat)) (rep.ty randomArgsTy))) ports.randomTag)))

def groupCode (signing : Bool) :=
  if signing then HandlerComponents.signing rep data cost primitive sampler
  else HandlerComponents.hash rep data cost primitive sampler

def group (signing : Bool) : Code Q unifSpec iface (rep.ty (HandlerComponents.argsStoreTy groupArgsTy))
    (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (Language.withContext (rep.ty storeTy) (Q.identity (rep.ty groupArgsTy))
    (groupCode rep data cost primitive sampler signing))
    (.first (rep.ty storeTy) (.atomic (Q.compose
      (QP.pair (QP.snd (rep.ty scalarGroupReplyTy) (rep.ty groupArgsTy))
        (QP.fst (rep.ty scalarGroupReplyTy) (rep.ty groupArgsTy))) (ports.scalarTag signing))))

def inner : Code Q unifSpec iface
    (StepClass.HasProd.prod (StepClass.HasSum.sum (rep.ty groupArgsTy) (rep.ty groupArgsTy)) (rep.ty storeTy))
    (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (.atomic (QD.distribute (rep.ty groupArgsTy) (rep.ty groupArgsTy) (rep.ty storeTy)))
    (.branch (group rep bd ports data cost primitive sampler false) (group rep bd ports data cost primitive sampler true))

def dispatch : Code Q unifSpec iface (StepClass.HasProd.prod (positions rep) (rep.ty storeTy))
    (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (.atomic (QD.distribute (rep.ty randomArgsTy)
    (StepClass.HasSum.sum (rep.ty groupArgsTy) (rep.ty groupArgsTy)) (rep.ty storeTy)))
    (.branch (random rep bd ports data cost primitive randomPorts) (inner rep bd ports data cost primitive sampler))

def code : Code Q unifSpec iface (StepClass.HasProd.prod bd.pos (rep.ty storeTy))
    (StepClass.HasProd.prod bd.idx (rep.ty storeTy)) :=
  .seq (.first (rep.ty storeTy) (.atomic ports.request)) (dispatch rep bd ports data cost primitive randomPorts sampler)

def source : QueryImpl (sourceSpec F G₁ M) (StateT ((G₁ × G₁) × EncodedState F G₁ M) ProbComp) := by
  intro ⟨⟨q, groups⟩, rows⟩
  cases q with
  | random n => exact fun saved =>
      (fun p => (⟨Fin.ofNat (n + 1) p.1.1, fun _ => p.1.2⟩, p.2)) <$>
        (HandlerComponents.random rep data cost primitive randomPorts).denote ((n, groups (), rows ()), saved)
  | hash m => exact fun saved =>
      (fun p => (decodeGroupReply p.1, p.2)) <$>
        (HandlerComponents.hash rep data cost primitive sampler).denote ((m, groups (), rows ()), saved)
  | sign m => exact fun saved =>
      (fun p => (decodeGroupReply p.1, p.2)) <$>
        (HandlerComponents.signing rep data cost primitive sampler).denote ((m, groups (), rows ()), saved)

omit QD in
theorem random_denote (args : Interface.Args Nat F G₁) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (random rep bd ports data cost primitive randomPorts).denote (args, saved) =
      (fun p => (Interface.randomTag (args, p.1), p.2)) <$>
        (HandlerComponents.random rep data cost primitive randomPorts).denote (args, saved) := by
  simp only [random, Language.withContext_denote, Code.denote, map_pure, bind_pure_comp, Functor.map_map]
  rfl

omit QD in
theorem group_denote (signing : Bool) (args : Interface.Args M F G₁) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (group rep bd ports data cost primitive sampler signing).denote (args, saved) =
      (fun p => (Interface.scalarTag signing (args, p.1), p.2)) <$>
        (groupCode rep data cost primitive sampler signing).denote (args, saved) := by
  simp only [group, Language.withContext_denote, Code.denote, map_pure, bind_pure_comp, Functor.map_map]
  rfl

theorem code_denote (q : SourceRequest F G₁ M) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (code rep bd ports data cost primitive randomPorts sampler).denote (q, saved) =
      (fun p => ((⟨q, p.1⟩ : SourceIndex F G₁ M), p.2)) <$>
        ((source rep data cost primitive randomPorts sampler q).run saved) := by
  rcases q with ⟨⟨q, groups⟩, rows⟩
  cases q with
  | random n =>
      simp only [code, dispatch, Code.denote, map_pure, pure_bind, encodeRequest, Sum.elim]
      rw [random_denote rep bd ports data cost primitive randomPorts]
      simp only [source, StateT.run, Functor.map_map, Interface.randomTag, request]
      rfl
  | hash m =>
      simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind, encodeRequest, Sum.elim]
      rw [group_denote rep bd ports data cost primitive sampler]
      simp only [source, StateT.run, Functor.map_map, groupCode, Interface.scalarTag, Bool.false_eq_true, ↓reduceIte, request]
      rfl
  | sign m =>
      simp only [code, dispatch, inner, Code.denote, map_pure, pure_bind, encodeRequest, Sum.elim]
      rw [group_denote rep bd ports data cost primitive sampler]
      simp only [source, StateT.run, Functor.map_map, groupCode, Interface.scalarTag, ↓reduceIte, request]
      rfl

variable [DecidableEq (SourceRequest F G₁ M)] (control : ControlCosts)
  (queryCost : (i : Nat) → unifSpec.Range i → Nat)

def executed : GeneralCaller.Handler (spec := sourceSpec F G₁ M)
    (StateT ((G₁ × G₁) × EncodedState F G₁ M) ProbComp) :=
  IndexedHandler.handler control queryCost (code rep bd ports data cost primitive randomPorts sampler) defaultReply

theorem code_executed_run (q : SourceRequest F G₁ M) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (code rep bd ports data cost primitive randomPorts sampler).run control queryCost (q, saved) =
      (fun p => (⟨(⟨q, p.1.value⟩, p.2), p.1.steps⟩ : Run (SourceIndex F G₁ M × ((G₁ × G₁) × EncodedState F G₁ M)))) <$>
        ((executed rep bd ports data cost primitive randomPorts sampler control queryCost q).run saved) := by
  apply IndexedHandler.handler_run
  exact IndexedHandler.matches_of_denote control queryCost _ (source rep data cost primitive randomPorts sampler)
    (code_denote rep bd ports data cost primitive randomPorts sampler)

theorem executed_erase (q : SourceRequest F G₁ M) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (fun p => (p.1.value, p.2)) <$>
      ((executed rep bd ports data cost primitive randomPorts sampler control queryCost q).run saved) =
        (source rep data cost primitive randomPorts sampler q).run saved :=
  IndexedHandler.handler_erase control queryCost _ defaultReply (source rep data cost primitive randomPorts sampler)
    (code_denote rep bd ports data cost primitive randomPorts sampler) q saved

variable [C.HasOption] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

def caller (fuel : Nat) : Code Q unifSpec iface (StepClass.HasProd.prod bd.input (rep.ty storeTy))
    (Caller.result (bd := bd) (rep.ty storeTy)) :=
  Caller.program R (rep.ty storeTy) (code rep bd ports data cost primitive randomPorts sampler) fuel

theorem caller_denote (fuel : Nat) (input : Input) (saved : (G₁ × G₁) × EncodedState F G₁ M) :
    (caller rep bd ports data cost primitive randomPorts sampler R fuel).denote (input, saved) =
      (R.machine.runWithInput (source rep data cost primitive randomPorts sampler) fuel input).run saved :=
  Caller.program_denote R (rep.ty storeTy) _ (source rep data cost primitive randomPorts sampler)
    (code_denote rep bd ports data cost primitive randomPorts sampler) fuel input saved

end Signatures.Runtime.SchnorrAGM.Native.Handler
