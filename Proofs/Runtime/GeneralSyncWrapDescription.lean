import Proofs.Runtime.GeneralSyncWrapRealizer
import Proofs.Runtime.GeneralSyncWrapCaps
import Proofs.Runtime.BackendExpressionSize

/-! # Stored code of the wrapper

The wrapper's three codes are wirings of the attacker's codes, the interface adapters, the
scheme's routines, a few primitives and the compiled finish. Each structural node costs one
allowance; the leaves are counted once per occurrence. -/

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation
open Signatures.Runtime.WeightedAGM (GeneralRequest GeneralIndex BoundedRandomReply generalSpec
  generalPositions NativePorts tagRandom tagHash tagSign)
open Signatures.Runtime.BackendProgram

namespace Signatures.Runtime.SyncWrapGeneral

set_option linter.unusedSectionVars false

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {randomBound : Nat}
  {rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)}
  {data : DataCode Q rep.data} {cost : PrimitiveCosts}
  {primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr)}
  {bdI : Boundary C (generalSpec (key.Value (cryptoBase F G₁ G₂ K M))
    (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound).toPFunctor (G₂ × G₂)
    (OutTy.Value (cryptoBase F G₁ G₂ K M))}
  {ports : NativePorts (Q := Q) rep key Weights.syncMessage bdI}
  {wports : WrapPorts rep ports}
  {correction finalFn : K × F → F} {keys : G₂ → G₂ × G₂}
  {code : SchemeCode (Q := Q) rep correction finalFn keys}
  {R : GeneralCaller.Caller (Q := Q) (bd := bdI)}
  (sizes : DescriptionSize Q) (allowance portSize routineSize instructionSize innerInit innerHead innerUpdate : Nat)

attribute [local implicit_reducible] PFunctor.Idx

/-- The description laws and leaf sizes the wrapper's stored code is measured with. -/
structure Descriptions : Prop where
  laws : LocalDescriptionLaws sizes allowance
  dataLaws : DataDescriptionLaws sizes rep.data data allowance
  dispatch : DispatchDescriptionLaws (Q := Q) sizes allowance
  optLaws : OptionDescriptionLaws (Q := Q) sizes allowance
  wrapPorts : WrapPortDescriptions rep ports wports sizes portSize
  scheme : SchemeDescriptions rep correction finalFn keys code sizes routineSize
  request : sizes.localSize ports.request ≤ portSize
  signTag : sizes.localSize ports.signTag ≤ portSize
  instructions : ∀ {a b : Ty CryptoAtom} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ instructionSize
  init : sizes.localSize R.initCode ≤ innerInit
  head : sizes.localSize R.headCode ≤ innerHead
  update : sizes.localSize R.updateCode ≤ innerUpdate

variable (D : Descriptions (rep := rep) (data := data) (primitive := primitive) (ports := ports) (wports := wports)
  (code := code) (R := R) sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate)

include D

local notation "LS" => sizes.localSize
local notation "prod" => StepClass.HasProd.prod
local notation "sum" => StepClass.HasSum.sum

/-- The compiled finish's description. -/
def finishDescription (allowance instructionSize : Nat) : Nat :=
  Expression.descriptionBound allowance (fun {_ _} _ => instructionSize) finExpr

theorem compile_finish_description :
    LS (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive finExpr) ≤
      finishDescription allowance instructionSize :=
  Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance D.laws D.dataLaws
    (fun {_ _} _ => instructionSize) (fun instr => D.instructions instr) finExpr

/-! ## Initialization -/

/-- The description budget of the wrapper's initialization. -/
def initDescription (allowance portSize routineSize innerInit : Nat) : Nat :=
  innerInit + routineSize + portSize + 8 * allowance

theorem initCode_description :
    LS (initCode rep data ports wports correction finalFn keys code R) ≤
      initDescription allowance portSize routineSize innerInit := by
  unfold initCode initDescription
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.pair_bound
      (D.laws.compose_bound D.scheme.keys (D.laws.compose_bound D.wrapPorts.input D.init))
      (D.laws.compose_bound (D.dataLaws.unit _) (D.dataLaws.nil _))) (D.dispatch.inl _ _)) (by omega)

/-! ## Readout -/

theorem periodCode_description : LS (periodCode rep) ≤ 3 * allowance := by
  unfold periodCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.fst _ _) (D.laws.fst _ _)) (by omega)

theorem hashPosCode_description : LS (hashPosCode rep ports wports) ≤ portSize + 4 * allowance := by
  unfold hashPosCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.dispatch.inr _ _) (D.laws.compose_bound (D.dispatch.inl _ _) D.wrapPorts.position))
    (by omega)

theorem finalPosCode_description : LS (finalPosCode rep ports wports) ≤ 2 * portSize + 9 * allowance := by
  unfold finalPosCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound D.wrapPorts.output (D.laws.compose_bound (periodCode_description sizes allowance
    portSize routineSize instructionSize innerInit innerHead innerUpdate D) (hashPosCode_description sizes allowance portSize
    routineSize instructionSize innerInit innerHead innerUpdate D))) (by omega)

theorem translatePosCode_description : LS (translatePosCode rep ports wports) ≤ 2 * portSize + 9 * allowance := by
  unfold translatePosCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound D.request (D.laws.compose_bound (D.laws.elim_bound (D.dispatch.inl _ _)
    (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound (D.dispatch.inr _ _) (D.dispatch.inl _ _))))
    D.wrapPorts.position)) (by omega)

theorem headReadyCode_description : LS (headReadyCode rep ports wports R) ≤ innerHead + 4 * portSize + 26 * allowance := by
  have hf := finalPosCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have ht := translatePosCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  unfold headReadyCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound D.head (D.laws.elim_bound
    (D.laws.compose_bound hf (D.dispatch.inr _ _)) (D.laws.compose_bound ht (D.dispatch.inr _ _))))) (by omega)

theorem headGotCode_description : LS (headGotCode rep ports wports R) ≤ innerHead + 2 * portSize + 16 * allowance := by
  have hf := finalPosCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  unfold headGotCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound D.head (D.laws.elim_bound
    (D.laws.compose_bound hf (D.dispatch.inr _ _)) (D.dispatch.inr _ _)))) (by omega)

theorem finishArgsCode_description : LS (finishArgsCode rep data) ≤ 11 * allowance := by
  unfold finishArgsCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) (D.laws.fst _ _))
    (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) (D.laws.snd _ _))
      (D.laws.pair_bound (D.laws.snd _ _) (D.dataLaws.unit _)))) (by omega)

theorem finalScalarCode_description : LS (finalScalarCode rep correction finalFn keys code) ≤ routineSize + 4 * allowance := by
  unfold finalScalarCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound (D.laws.fst _ _) D.scheme.fin)) (by omega)

theorem finishCode_description :
    LS (finishCode rep data cost primitive ports wports correction finalFn keys code) ≤
      2 * portSize + routineSize + finishDescription allowance instructionSize + 25 * allowance := by
  have ha := finishArgsCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hs := finalScalarCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hc := compile_finish_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  unfold finishCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) D.wrapPorts.output)
    (D.laws.snd _ _)) (D.laws.compose_bound (D.laws.pair_bound (D.laws.identity _) hs)
      (D.laws.compose_bound ha (D.laws.compose_bound hc D.wrapPorts.encode)))) (by omega)

/-- The description budget of the wrapper's readout. -/
def headDescription (allowance portSize routineSize instructionSize innerHead : Nat) : Nat :=
  2 * innerHead + 8 * portSize + routineSize + finishDescription allowance instructionSize + 71 * allowance

theorem headCode_description :
    LS (headCode rep data cost primitive ports wports correction finalFn keys code R) ≤
      headDescription allowance portSize routineSize instructionSize innerHead := by
  have hr := headReadyCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hg := headGotCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hf := finishCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hd : LS (headDoneCode rep data cost primitive ports wports correction finalFn keys code) ≤
      2 * portSize + routineSize + finishDescription allowance instructionSize + 27 * allowance := by
    unfold headDoneCode
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.compose_bound hf (D.dispatch.inl _ _)) (by omega)
  unfold headCode headDescription
  refine (DescriptionSize.castFunction sizes _ _).le.trans ?_
  exact le_trans (D.laws.elim_bound hr (D.laws.elim_bound hg hd)) (by omega)

/-! ## Transition -/

theorem markHashCode_description : LS (markHashCode rep data cost primitive) ≤ instructionSize + 2 * allowance := by
  unfold markHashCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.pair_bound (D.dataLaws.bool _) (D.instructions _)) (by omega)

theorem markSignCode_description : LS (markSignCode rep data correction finalFn keys code) ≤ routineSize + 4 * allowance := by
  unfold markSignCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.pair_bound (D.laws.compose_bound (D.dataLaws.unit _) (D.dataLaws.bool _)) D.scheme.corr) (by omega)

theorem readyAgainCode_description : LS (readyAgainCode rep R) ≤ 3 * allowance := by
  unfold readyAgainCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.dispatch.inl _ _) (D.dispatch.some _)) (by omega)

theorem dropPointCode_description : LS (dropPointCode rep R) ≤ 11 * allowance := by
  unfold dropPointCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.pair_bound (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) (D.laws.fst _ _))
    (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound (D.laws.snd _ _) (D.laws.snd _ _)))) (D.laws.snd _ _))
    (by omega)

theorem fedCode_description : LS (fedCode rep R) ≤ innerUpdate + 6 * allowance := by
  unfold fedCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) (D.laws.fst _ _))
    (D.laws.snd _ _)) D.update) (by omega)

theorem stepReadyCode_description {update : List (Mark F) → List (Mark F)} (markCode : Q.Realizer (marksRep rep) (marksRep rep) update)
    {Dm : Nat} (hm : LS markCode ≤ Dm) : LS (stepReadyCode rep R markCode) ≤ innerUpdate + Dm + 16 * allowance := by
  have hf := fedCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have ha := readyAgainCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  unfold stepReadyCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.pair_bound hf (D.laws.compose_bound (D.laws.fst _ _)
    (D.laws.compose_bound (D.laws.snd _ _) hm))) (D.optLaws.bindContext _)) (by omega)

theorem keepMarksCode_description : LS (keepMarksCode rep) ≤ allowance := D.laws.identity _

theorem recordHashCode_description : LS (recordHashCode rep data cost primitive) ≤ instructionSize + 8 * allowance := by
  have hm := markHashCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  unfold recordHashCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.pair_bound (D.laws.compose_bound (D.dataLaws.unit _) hm) (D.laws.identity _))
    (D.dataLaws.cons _)) (by omega)

theorem elimContext_description {A B E Dt : Type} {a : C.Str A} {b : C.Str B} {e : C.Str E} {d : C.Str Dt}
    {f : A × E → Dt} {g : B × E → Dt} (left : Q.Realizer (prod a e) d f) (right : Q.Realizer (prod b e) d g)
    {L R' : Nat} (hl : LS left ≤ L) (hr : LS right ≤ R') :
    LS (QuantitativeStepClass.IsDistributive.elimContext Q QD left right) ≤ L + R' + 3 * allowance := by
  unfold QuantitativeStepClass.IsDistributive.elimContext
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.dispatch.distribute _ _ _) (D.laws.elim_bound hl hr)) (by omega)

theorem expectHashCode_description {E : Type} {e : C.Str E} {expected : E → K} (expectedCode : Q.Realizer e (rep.ty key) expected)
    {next : (K × G₁) × E → State R.machine (F := F)}
    (nextCode : Q.Realizer (prod (prod (rep.ty key) (rep.ty point₁)) e) (stateRep rep R) next)
    {De Dn : Nat} (he : LS expectedCode ≤ De) (hn : LS nextCode ≤ Dn) :
    LS (expectHashCode rep data cost primitive ports R expectedCode nextCode) ≤ De + Dn + instructionSize + 24 * allowance := by
  have hcompare : LS (Q.compose
      (QP.pair (Q.compose (QP.pair (Q.compose (QP.fst (prod (rep.ty key) (rep.ty point₁)) e) (QP.fst (rep.ty key) (rep.ty point₁)))
          (Q.compose (QP.snd (prod (rep.ty key) (rep.ty point₁)) e) expectedCode)) (primitive CryptoOp.keyEq))
        (Q.identity (prod (prod (rep.ty key) (rep.ty point₁)) e)))
      (Q.compose (data.select (prod (prod (rep.ty key) (rep.ty point₁)) e))
        (QS.elim (Q.compose nextCode (OC.someCode (stateRep rep R)))
          (QO.none (prod (prod (rep.ty key) (rep.ty point₁)) e) (stateRep rep R))))) ≤ De + Dn + instructionSize + 16 * allowance :=
    le_trans (D.laws.compose_bound (D.laws.pair_bound (D.laws.compose_bound (D.laws.pair_bound
      (D.laws.compose_bound (D.laws.fst _ _) (D.laws.fst _ _)) (D.laws.compose_bound (D.laws.snd _ _) he)) (D.instructions _))
      (D.laws.identity _)) (D.laws.compose_bound (D.dataLaws.select _) (D.laws.elim_bound
        (D.laws.compose_bound hn (D.dispatch.some _)) (D.dispatch.none _ _)))) (by omega)
  unfold expectHashCode
  dsimp only
  rw [DescriptionSize.castFunction]
  exact le_trans (elimContext_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D _ _
    (D.dispatch.none _ _) (elimContext_description sizes allowance portSize routineSize instructionSize innerInit innerHead
      innerUpdate D _ _ hcompare (D.dispatch.none _ _))) (by omega)

theorem decodedCode_description {E : Type} (e : C.Str E)
    {idxOf : E → GeneralIndex (key.Value (cryptoBase F G₁ G₂ K M)) (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound}
    (idxCode : Q.Realizer e bdI.idx idxOf) {Di : Nat} (hi : LS idxCode ≤ Di) :
    LS (decodedCode rep ports wports e idxCode) ≤ Di + portSize + 3 * allowance := by
  unfold decodedCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.pair_bound (D.laws.compose_bound hi D.wrapPorts.reply) (D.laws.identity _)) (by omega)

theorem finishReadyCode_description :
    LS (finishReadyCode rep data cost primitive ports wports R) ≤ 2 * portSize + instructionSize + 52 * allowance := by
  have he : LS (finishExpectedCode rep ports wports R) ≤ portSize + 6 * allowance := by
    unfold finishExpectedCode
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound D.wrapPorts.output
      (periodCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D))) (by omega)
  have hn : LS (finishNextCode rep R) ≤ 15 * allowance := by
    unfold finishNextCode
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.compose_bound (D.laws.pair_bound (D.laws.compose_bound (D.laws.snd _ _) (D.laws.fst _ _))
      (D.laws.compose_bound (D.laws.snd _ _) (D.laws.compose_bound (D.laws.snd _ _)
        (D.laws.compose_bound (D.laws.fst _ _) (D.laws.snd _ _)))))
      (D.laws.compose_bound (D.dispatch.inr _ _) (D.dispatch.inr _ _))) (by omega)
  have hi : LS (Q.compose (QP.snd bdI.out (readyCtx rep R)) (readyIdxCode rep R)) ≤ 3 * allowance := by
    unfold readyIdxCode
    exact le_trans (D.laws.compose_bound (D.laws.snd _ _) (D.laws.snd _ _)) (by omega)
  have hd := decodedCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D _ _ hi
  have hx := expectHashCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
    (finishExpectedCode rep ports wports R) (finishNextCode rep R) he hn
  unfold finishReadyCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound hd hx) (by omega)

theorem holdHashCode_description :
    LS (holdHashCode rep data cost primitive ports wports R) ≤ portSize + instructionSize + 57 * allowance := by
  have he : LS (holdExpectedCode rep R) ≤ 3 * allowance := by
    unfold holdExpectedCode
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.compose_bound (D.laws.fst _ _) (D.laws.fst _ _)) (by omega)
  have hn : LS (holdNextCode rep R) ≤ 23 * allowance := by
    unfold holdNextCode
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.compose_bound (D.laws.pair_bound
      (D.laws.compose_bound (D.laws.snd _ _) (D.laws.compose_bound (D.laws.snd _ _)
        (D.laws.compose_bound (D.laws.fst _ _) (D.laws.fst _ _))))
      (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) (D.laws.snd _ _))
        (D.laws.compose_bound (D.laws.snd _ _) (D.laws.compose_bound (D.laws.snd _ _)
          (D.laws.compose_bound (D.laws.fst _ _) (D.laws.snd _ _))))))
      (D.laws.compose_bound (D.dispatch.inl _ _) (D.dispatch.inr _ _))) (by omega)
  have hi : LS (Q.compose (QP.snd (rep.ty Weights.syncMessage) (readyCtx rep R)) (readyIdxCode rep R)) ≤ 3 * allowance := by
    unfold readyIdxCode
    exact le_trans (D.laws.compose_bound (D.laws.snd _ _) (D.laws.snd _ _)) (by omega)
  have hd := decodedCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D _ _ hi
  have hx := expectHashCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
    (holdExpectedCode rep R) (holdNextCode rep R) he hn
  unfold holdHashCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound hd hx) (by omega)

theorem pairRightRequest_description {E : Type} (e : C.Str E) :
    LS (QuantitativeStepClass.HasProd.pairRight Q QP (d := e) ports.request) ≤ portSize + 4 * allowance := by
  unfold QuantitativeStepClass.HasProd.pairRight
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) D.request) (D.laws.snd _ _)) (by omega)

theorem requestReadyCode_description :
    LS (requestReadyCode rep data cost primitive ports wports R) ≤
      2 * innerUpdate + 2 * instructionSize + 2 * portSize + 130 * allowance := by
  have hk := stepReadyCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
    (keepMarksCode rep) (keepMarksCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D)
  have hr := stepReadyCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
    (recordHashCode rep data cost primitive)
    (recordHashCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D)
  have hh := holdHashCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hp := pairRightRequest_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
    (readyCtx rep R)
  unfold requestReadyCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound hp (elimContext_description sizes allowance portSize routineSize instructionSize innerInit
    innerHead innerUpdate D _ _ (elimContext_description sizes allowance portSize routineSize instructionSize innerInit innerHead
      innerUpdate D _ _ (D.laws.compose_bound (D.laws.snd _ _) hk) (D.laws.compose_bound (D.laws.snd _ _) hr)) hh)) (by omega)

theorem updateReadyCode_description :
    LS (updateReadyCode rep data cost primitive ports wports R) ≤
      innerHead + 2 * innerUpdate + 3 * instructionSize + 4 * portSize + 200 * allowance := by
  have hf := finishReadyCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hr := requestReadyCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hw : LS (QuantitativeStepClass.HasProd.withInput Q QP
      (Q.compose (QP.fst (readyRep rep R) bdI.idx) (Q.compose (QP.fst R.state (marksRep rep)) R.headCode))) ≤
      innerHead + 6 * allowance := by
    unfold QuantitativeStepClass.HasProd.withInput
    exact le_trans (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound (D.laws.fst _ _) D.head))
      (D.laws.identity _)) (by omega)
  unfold updateReadyCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound hw (elimContext_description sizes allowance portSize routineSize instructionSize innerInit
    innerHead innerUpdate D _ _ hf hr)) (by omega)

theorem correctedCode_description :
    LS (correctedCode rep cost primitive correction finalFn keys code R) ≤ routineSize + 2 * instructionSize + 20 * allowance := by
  have hh : LS (heldCode rep R) ≤ 9 * allowance := by
    unfold heldCode
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.compose_bound (D.laws.snd _ _) (D.laws.compose_bound (D.laws.snd _ _)
      (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound (D.laws.snd _ _) (D.laws.fst _ _))))) (by omega)
  unfold correctedCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) (D.laws.snd _ _))
    (D.laws.compose_bound (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _)
      (D.laws.compose_bound (D.laws.fst _ _) D.scheme.corr)) hh) (D.instructions _))) (D.instructions _)) (by omega)

theorem signedCode_description :
    LS (signedCode rep data cost primitive ports correction finalFn keys code R) ≤
      innerUpdate + 2 * routineSize + 2 * instructionSize + portSize + 60 * allowance := by
  have hc := correctedCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hm := markSignCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have ha := readyAgainCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hfed : LS (fedSignCode rep cost primitive ports correction finalFn keys code R) ≤
      innerUpdate + routineSize + 2 * instructionSize + portSize + 34 * allowance := by
    unfold fedSignCode
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.compose_bound (D.laws.pair_bound
      (D.laws.compose_bound (D.laws.snd _ _) (D.laws.compose_bound (D.laws.snd _ _)
        (D.laws.compose_bound (D.laws.fst _ _) (D.laws.fst _ _))))
      (D.laws.compose_bound (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) (D.laws.fst _ _)) hc) D.signTag))
      D.update) (by omega)
  have hmarked : LS (markedCode rep data correction finalFn keys code R) ≤ routineSize + 20 * allowance := by
    unfold markedCode
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.compose_bound (D.laws.pair_bound
      (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound (D.laws.fst _ _) hm))
      (D.laws.compose_bound (D.laws.snd _ _) (D.laws.compose_bound (D.laws.snd _ _)
        (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound (D.laws.snd _ _) (D.laws.snd _ _))))))
      (D.dataLaws.cons _)) (by omega)
  unfold signedCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound (D.laws.pair_bound hfed hmarked) (D.optLaws.bindContext _)) (by omega)

theorem requestGotCode_description :
    LS (requestGotCode rep data cost primitive ports wports correction finalFn keys code R) ≤
      3 * innerUpdate + 2 * routineSize + 3 * instructionSize + 3 * portSize + 180 * allowance := by
  have hk := stepReadyCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
    (keepMarksCode rep) (keepMarksCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D)
  have hr := stepReadyCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
    (recordHashCode rep data cost primitive)
    (recordHashCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D)
  have hdp := dropPointCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hs := signedCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hp := pairRightRequest_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
    (gotCtx rep R)
  have hi : LS (Q.compose (QP.snd (rep.ty Weights.syncMessage) (gotCtx rep R)) (QP.snd (gotRep rep R) bdI.idx)) ≤ 3 * allowance :=
    le_trans (D.laws.compose_bound (D.laws.snd _ _) (D.laws.snd _ _)) (by omega)
  have hd := decodedCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D _ _ hi
  have hfeed : LS (feedSignCode rep data cost primitive ports wports correction finalFn keys code R) ≤
      innerUpdate + 2 * routineSize + 2 * instructionSize + 2 * portSize + 75 * allowance := by
    unfold feedSignCode
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.compose_bound hd (elimContext_description sizes allowance portSize routineSize instructionSize innerInit
      innerHead innerUpdate D _ _ (D.dispatch.none _ _) (elimContext_description sizes allowance portSize routineSize instructionSize
        innerInit innerHead innerUpdate D _ _ (D.dispatch.none _ _) hs))) (by omega)
  unfold requestGotCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound hp (elimContext_description sizes allowance portSize routineSize instructionSize innerInit
    innerHead innerUpdate D _ _ (elimContext_description sizes allowance portSize routineSize instructionSize innerInit innerHead
      innerUpdate D _ _ (D.laws.compose_bound (D.laws.snd _ _) (D.laws.compose_bound hdp hk))
      (D.laws.compose_bound (D.laws.snd _ _) (D.laws.compose_bound hdp hr))) hfeed)) (by omega)

theorem updateGotCode_description :
    LS (updateGotCode rep data cost primitive ports wports correction finalFn keys code R) ≤
      innerHead + 3 * innerUpdate + 2 * routineSize + 4 * instructionSize + 5 * portSize + 270 * allowance := by
  have hf := finishReadyCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hg := requestGotCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hdp := dropPointCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hw : LS (QuantitativeStepClass.HasProd.withInput Q QP
      (Q.compose (QP.fst (gotRep rep R) bdI.idx) (Q.compose (QP.fst R.state (prod (rep.ty point₁) (marksRep rep))) R.headCode))) ≤
      innerHead + 6 * allowance := by
    unfold QuantitativeStepClass.HasProd.withInput
    exact le_trans (D.laws.pair_bound (D.laws.compose_bound (D.laws.fst _ _) (D.laws.compose_bound (D.laws.fst _ _) D.head))
      (D.laws.identity _)) (by omega)
  have hpl : LS (QuantitativeStepClass.HasProd.pairLeft Q QP (d := bdI.out) (dropPointCode rep R)) ≤ 15 * allowance := by
    unfold QuantitativeStepClass.HasProd.pairLeft
    rw [DescriptionSize.castFunction]
    exact le_trans (D.laws.pair_bound (D.laws.fst _ _) (D.laws.compose_bound (D.laws.snd _ _) hdp)) (by omega)
  have hleft : LS (Q.compose (QuantitativeStepClass.HasProd.pairLeft Q QP (d := bdI.out) (dropPointCode rep R))
      (finishReadyCode rep data cost primitive ports wports R)) ≤ 2 * portSize + instructionSize + 68 * allowance :=
    le_trans (D.laws.compose_bound hpl hf) (by omega)
  have hctx := elimContext_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D _ _
    hleft hg
  unfold updateGotCode
  rw [DescriptionSize.castFunction]
  exact le_trans (D.laws.compose_bound hw hctx) (by omega)

/-- The description budget of the wrapper's transition. -/
def updateDescription (allowance portSize routineSize instructionSize innerHead innerUpdate : Nat) : Nat :=
  2 * innerHead + 5 * innerUpdate + 2 * routineSize + 7 * instructionSize + 9 * portSize + 480 * allowance

theorem updateCode_description :
    LS (updateCode rep data cost primitive ports wports correction finalFn keys code R) ≤
      updateDescription allowance portSize routineSize instructionSize innerHead innerUpdate := by
  have hr := updateReadyCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hg := updateGotCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  unfold updateCode updateDescription
  refine (DescriptionSize.castFunction sizes _ _).le.trans ?_
  exact le_trans (D.laws.compose_bound (D.dispatch.distribute _ _ _) (D.laws.elim_bound hr
    (D.laws.compose_bound (D.dispatch.distribute _ _ _) (D.laws.elim_bound hg (D.dispatch.none _ _))))) (by omega)

/-- The wrapper's stored code, as the pipeline weighs it: initialization, twice the readout, the
transition. -/
def wrapCodeLimit (allowance portSize routineSize instructionSize innerCode : Nat) : Nat :=
  5 * innerCode + 2 * (headDescription allowance portSize routineSize instructionSize 0) +
    initDescription allowance portSize routineSize 0 + updateDescription allowance portSize routineSize instructionSize 0 0

theorem storedCode (innerCode : Nat) (hinner : innerInit + 2 * innerHead + innerUpdate ≤ innerCode) :
    LS (initCode rep data ports wports correction finalFn keys code R) +
      2 * LS (headCode rep data cost primitive ports wports correction finalFn keys code R) +
      LS (updateCode rep data cost primitive ports wports correction finalFn keys code R) ≤
      wrapCodeLimit allowance portSize routineSize instructionSize innerCode := by
  have hi := initCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hh := headCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  have hu := updateCode_description sizes allowance portSize routineSize instructionSize innerInit innerHead innerUpdate D
  unfold wrapCodeLimit initDescription headDescription updateDescription at *
  omega

end Signatures.Runtime.SyncWrapGeneral
