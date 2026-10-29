import Proofs.Runtime.GeneralSyncWrapUpdateCost5

/-! # Cost of the wrapper's transition, part six: the dispatch

The waiting state's transition dispatches the signature reply, and the transition itself selects
the ready or waiting case. At every enabled step the cost is within one budget. -/

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation
open Signatures.Runtime.WeightedAGM (GeneralRequest GeneralIndex BoundedRandomReply generalSpec
  generalPositions NativePorts tagRandom tagHash tagSign)
open Signatures.Runtime.BackendProgram
open Signatures.Runtime.BackendProgram.FrameCost (fee)

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
  {overhead : Nat → Nat}
  {primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr)}
  {header : Nat}
  {width cap stateWidth headWidth routeWidth outputWidth finishedRoute : Nat}
  {adapterTime routineTime opTime comparisonTime work : Nat}
  (S : Caps rep data cost primitive ports wports correction finalFn keys code primitiveBound overhead header
    width cap stateWidth headWidth routeWidth outputWidth finishedRoute adapterTime routineTime opTime comparisonTime)

attribute [local implicit_reducible] PFunctor.Idx

include S

local notation "prod" => StepClass.HasProd.prod
local notation "sum" => StepClass.HasSum.sum
local notation "opt" => StepClass.HasOption.option
local notation "WF" => wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute
local notation "tick" => fee overhead (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "pRep" => rep.ty point₁
local notation "kRep" => rep.ty key
local notation "msgRep" => rep.ty Weights.syncMessage
local notation "mRep" => marksRep rep
local notation "boundedRep" => rep.ty (boundedNat randomBound)
local notation "COMPOSE" => FrameCost.compose_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "PAIR" => FrameCost.pair_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "FST" => FrameCost.fst_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "SND" => FrameCost.snd_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "IDENT" => FrameCost.identity_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "ELIML" => FrameCost.elim_inl_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "ELIMR" => FrameCost.elim_inr_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "INL" => FrameCost.inl_le S.dispatch S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "INR" => FrameCost.inr_le S.dispatch S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "NONE" => FrameCost.none_le S.dispatch S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "SOME" => FrameCost.some_le S.dispatch S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "DISTRIBUTE" => FrameCost.distribute_le S.dispatch S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "SELECT" => FrameCost.select_le S.dataLaws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "UNITC" => FrameCost.unit_le S.dataLaws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "BOOLC" => FrameCost.bool_le S.dataLaws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "CONSC" => FrameCost.cons_le S.dataLaws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "BIND" => FrameCost.bindContext_le S.optLaws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "CAST" => FrameCost.castFunction_le

/-- The representation and value abbreviations to unfold before arithmetic. -/
local macro "nz" : tactic => `(tactic| (
  (try dsimp only [readyRep, gotRep, doneRep, stateRep, marksRep, posRep, replyRep, readyCtx, gotCtx, signCtx, signFrame,
    outerBoundary, Weights.syncMessage, OutTy, AGM.outputTy, markTy, LanguageRepresentation.ty, LanguageRepresentation.env,
    PFunctor.DynSystem.DynComputation.Boundary.head, PFunctor.DynSystem.DynComputation.Boundary.stateIdx,
    WeightedAGM.generalPositions, finalIndex, wrapFrame, ready, gotHash, done, markHash, markSign, tagSign, tagHash, decodeIdx,
    Sum.elim_inl, Sum.elim_inr, Option.bind, Option.map, Function.comp_def, id] at *);
  (try simp only [arithmetic, eq_self_iff_true, decide_true, ite_true, Sum.elim_inl, Sum.elim_inr] at *)))

/-- Normalize the goal alone, then close it by arithmetic over the normalized facts. -/
local macro "szg" : tactic => `(tactic| (
  (try dsimp only [readyRep, gotRep, doneRep, stateRep, marksRep, posRep, replyRep, readyCtx, gotCtx, signCtx, signFrame,
    outerBoundary, Weights.syncMessage, OutTy, AGM.outputTy, markTy, LanguageRepresentation.ty, LanguageRepresentation.env,
    PFunctor.DynSystem.DynComputation.Boundary.head, PFunctor.DynSystem.DynComputation.Boundary.stateIdx,
    WeightedAGM.generalPositions, finalIndex, wrapFrame, ready, gotHash, done, markHash, markSign, tagSign, tagHash, decodeIdx,
    Sum.elim_inl, Sum.elim_inr, Option.bind, Option.map, Function.comp_def, id]);
  (try simp only [arithmetic, eq_self_iff_true, decide_true, ite_true, Sum.elim_inl, Sum.elim_inr]);
  omega))

/-- Normalize everything, then close by arithmetic. -/
local macro "sz" : tactic => `(tactic| (nz; omega))




/-! ## Dispatching the signature reply -/

/-- Decoding the signature reply and dispatching it to the signed continuation. -/
theorem feedSignCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (h : G₁) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width) (σ : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx_def : idx = ⟨.inr m, σ⟩)
    (hupd : Q.cost R.updateCode (s, tagSign (m, σ + correction m • h)) ≤ work) (s' : R.machine.State)
    (hnext : R.machine.update? (s, tagSign (m, σ + correction m • h)) = some s') (hs' : Q.size R.state s' ≤ stateWidth) :
    Q.cost (feedSignCode rep data cost primitive ports wports correction finalFn keys code R) (m, ((s, h, marks), idx)) ≤
      work + 2 * routineTime + 2 * opTime + 2 * adapterTime + 74 * tick := by
  have hh := S.fcaps.hdr
  have hσ := S.point₁ σ
  have hidx : Q.size bdI.idx idx ≤ 8 * width := by rw [hidx_def]; exact (S.pcaps.signTag m σ hmsg hσ).1
  obtain ⟨hframe, hsctx, hctx, hgot⟩ := signFrame_sizes S s hs h marks hml m hmsg σ idx hidx
  have hmσ := pair_size S.sizes msgRep pRep m σ hmsg hσ
  obtain ⟨hm, hm', hmark⟩ := marks_sizes S marks hml (markSign correction m)
  have hres : Q.size (opt R.state) (R.machine.update? (s, tagSign (m, σ + correction m • h))) ≤ stateWidth + header := by
    rw [hnext]; exact some_size S.sizes R.state s' hs'
  have hp' := pair_size S.sizes R.state mRep s' (markSign correction m :: marks) hs' hm'
  have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s', markSign correction m :: marks) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (ready R.machine s' (markSign correction m :: marks)) le_rfl
  have hval : Q.size (opt (stateRep rep R))
      ((R.machine.update? (s, tagSign (m, σ + correction m • h))).map fun x => ready R.machine x (markSign correction m :: marks)) ≤
      WF := by
    rw [hnext]; sz
  have hval2 : Q.size (opt (stateRep rep R))
      ((R.machine.update? (s, tagSign (m, σ + correction m • h))).bind fun x =>
        some (ready R.machine x (markSign correction m :: marks))) ≤ WF := by
    rw [hnext]; sz
  -- the index code and the decoded reply
  have tidx : Q.cost (Q.compose (QP.snd msgRep (gotCtx rep R)) (QP.snd (gotRep rep R) bdI.idx)) (m, ((s, h, marks), idx)) ≤
      3 * tick := by
    nz
    have a1 := SND msgRep (gotCtx rep R) (m, ((s, h, marks), idx)) (by szg) (by szg)
    have a2 := SND (gotRep rep R) bdI.idx ((s, h, marks), idx) (by szg) (by szg)
    have := COMPOSE _ _ (m, ((s, h, marks), idx)) a1 a2 (by szg) (by szg) (by szg)
    sz
  obtain ⟨tdec, hreply⟩ := decodedCode_cost S (signCtx rep R) (Q.compose (QP.snd msgRep (gotCtx rep R)) (QP.snd (gotRep rep R) bdI.idx))
    (m, ((s, h, marks), idx)) (by sz) tidx hidx
  have hrepl := pair_size S.sizes (replyRep rep ports) (signCtx rep R) _ (m, ((s, h, marks), idx)) hreply le_rfl
  have tsigned := signedCode_cost S s hs h marks hml m hmsg σ idx hidx hupd s' hnext hs'
  subst hidx_def
  have hrp := inr_size S.sizes (prod kRep pRep) (prod msgRep pRep) (m, σ) le_rfl
  have hrp' := inr_size S.sizes ports.randomReply (sum (prod kRep pRep) (prod msgRep pRep)) (Sum.inr (m, σ)) le_rfl
  have hd1 := pair_size S.sizes (sum (prod kRep pRep) (prod msgRep pRep)) (signCtx rep R) (Sum.inr (m, σ)) (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))) le_rfl le_rfl
  have hd2 := inr_size S.sizes (prod ports.randomReply (signCtx rep R)) (prod (sum (prod kRep pRep) (prod msgRep pRep)) (signCtx rep R))
    (Sum.inr (m, σ), (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound)))) le_rfl
  have hd3 := inr_size S.sizes (prod (prod kRep pRep) (signCtx rep R)) (prod (prod msgRep pRep) (signCtx rep R))
    ((m, σ), (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound)))) le_rfl
  nz
  unfold feedSignCode
  apply CAST
  have d1 := DISTRIBUTE ports.randomReply (sum (prod kRep pRep) (prod msgRep pRep)) (signCtx rep R)
    (Sum.inr (Sum.inr (m, σ)), (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound)))) (by szg) (by szg)
  have d2 := DISTRIBUTE (prod kRep pRep) (prod msgRep pRep) (signCtx rep R) (Sum.inr (m, σ), (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound)))) (by szg) (by szg)
  have e2 := ELIMR (QO.none (prod (prod kRep pRep) (signCtx rep R)) (stateRep rep R)) _ ((m, σ), (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound)))) tsigned
    (by szg) (by first | exact hval | exact hval2 | szg)
  have c2 := COMPOSE _ _ (Sum.inr (m, σ), (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound)))) d2 e2 (by szg) (by szg) (by first | exact hval | exact hval2 | szg)
  exact le_trans (COMPOSE _ _ (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))) tdec
    (le_trans (CAST _ _ _ (COMPOSE _ _ (Sum.inr (Sum.inr (m, σ)), (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound)))) d1
      (ELIMR (QO.none (prod ports.randomReply (signCtx rep R)) (stateRep rep R)) _ (Sum.inr (m, σ), (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))))
        (CAST _ _ _ c2) (by szg) (by first | exact hval | exact hval2 | szg))
      (by szg) (by szg) (by first | exact hval | exact hval2 | szg))) le_rfl)
    (by szg) (by szg) (by first | exact hval | exact hval2 | szg)) (by szg)

/-- The waiting state's pending request is the signing one: dispatch the signature reply. -/
theorem requestGotCode_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s) (h : G₁)
    (marks : List (Mark F)) (hml : marks.length ≤ cap) (m : K × F)
    (hv : ∃ next, R.machine.view s = .inr ⟨.inr m, next⟩) (σ : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx_def : idx = ⟨.inr m, σ⟩)
    (hupd : Q.cost R.updateCode (s, tagSign (m, σ + correction m • h)) ≤ work) (s' : R.machine.State)
    (hnext : R.machine.update? (s, tagSign (m, σ + correction m • h)) = some s') (hs' : Q.size R.state s' ≤ stateWidth) :
    Q.cost (requestGotCode rep data cost primitive ports wports correction finalFn keys code R) (.inr m, ((s, h, marks), idx)) ≤
      work + 2 * routineTime + 2 * opTime + 3 * adapterTime + 82 * tick := by
  obtain ⟨next, hv⟩ := hv
  have hreq := hs.request (.inr m) next hv
  have hmsg : Q.size msgRep m ≤ width := hreq
  have hh := S.fcaps.hdr
  have hσ := S.point₁ σ
  have hidx : Q.size bdI.idx idx ≤ 8 * width := by rw [hidx_def]; exact (S.pcaps.signTag m σ hmsg hσ).1
  obtain ⟨hframe, hsctx, hctx, hgot⟩ := signFrame_sizes S s hs.state h marks hml m hmsg σ idx hidx
  obtain ⟨tpr, hbd, hdec⟩ := pairRightRequest_cost S (gotCtx rep R) (.inr m) hreq ((s, h, marks), idx) (by sz)
  have hposctx := pair_size S.sizes (posRep rep) (gotCtx rep R) (.inr m) ((s, h, marks), idx) hdec le_rfl
  have hbdctx := pair_size S.sizes bdI.pos (gotCtx rep R) (.inr m) ((s, h, marks), idx) hbd le_rfl
  have hdist := inr_size S.sizes (prod (sum boundedRep kRep) (gotCtx rep R)) (prod msgRep (gotCtx rep R)) (m, ((s, h, marks), idx)) le_rfl
  obtain ⟨hm, hm', hmark⟩ := marks_sizes S marks hml (markSign correction m)
  have hp' := pair_size S.sizes R.state mRep s' (markSign correction m :: marks) hs' hm'
  have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s', markSign correction m :: marks) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (ready R.machine s' (markSign correction m :: marks)) le_rfl
  have hval : Q.size (opt (stateRep rep R))
      ((R.machine.update? (s, tagSign (m, σ + correction m • h))).map fun x => ready R.machine x (markSign correction m :: marks)) ≤
      WF := by
    rw [hnext]; sz
  have tfeed := feedSignCode_cost S s hs.state h marks hml m hmsg σ idx hidx_def hupd s' hnext hs'
  subst hidx_def
  nz
  unfold requestGotCode
  apply CAST
  have a6 := DISTRIBUTE (sum boundedRep kRep) msgRep (gotCtx rep R) (Sum.inr m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))) (by szg) (by szg)
  exact le_trans (COMPOSE _ _ (Sum.inr m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))) tpr
    (le_trans (CAST _ _ _ (COMPOSE _ _ (Sum.inr m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))) a6
      (ELIMR _ (feedSignCode rep data cost primitive ports wports correction finalFn keys code R) (m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))) tfeed
        (by szg) (by first | exact hval | szg))
      (by szg) (by szg) (by first | exact hval | szg))) le_rfl)
    (by szg) (by szg) (by first | exact hval | szg)) (by szg)

/-- Reading the attacker's readout from a waiting state while retaining the context. -/
theorem withInputHeadGot_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s) (h : G₁)
    (marks : List (Mark F)) (hml : marks.length ≤ cap) (idx : GeneralIndex K (K × F) G₁ randomBound)
    (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.cost (QuantitativeStepClass.HasProd.withInput Q QP
      (Q.compose (QP.fst (gotRep rep R) bdI.idx) (Q.compose (QP.fst R.state (prod pRep mRep)) R.headCode))) ((s, h, marks), idx) ≤
      work + 6 * tick := by
  have hh := S.fcaps.hdr
  have hHR := S.headRoute
  have hss := hs.state
  have hsh := hs.head
  have hpt := S.point₁ h
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hhm := pair_size S.sizes pRep mRep h marks hpt hm
  have hgot := pair_size S.sizes R.state (prod pRep mRep) s (h, marks) hss hhm
  have hctx := pair_size S.sizes (gotRep rep R) bdI.idx (s, h, marks) idx le_rfl hidx
  have hout := pair_size S.sizes bdI.head (gotCtx rep R) (R.machine.head s) ((s, h, marks), idx) hsh le_rfl
  nz
  unfold QuantitativeStepClass.HasProd.withInput
  have a1 := FST (gotRep rep R) bdI.idx ((s, h, marks), idx) (by szg) (by szg)
  have a2 := FST R.state (prod pRep mRep) (s, h, marks) (by szg) (by szg)
  have a3 := COMPOSE _ _ (s, h, marks) a2 hs.headCost (by szg) (by szg) (by szg)
  have a4 := COMPOSE _ _ ((s, h, marks), idx) a1 a3 (by szg) (by szg) (by szg)
  have a5 := IDENT (gotCtx rep R) ((s, h, marks), idx) (by szg)
  have := PAIR _ _ ((s, h, marks), idx) a4 a5 (by szg) (by szg)
  sz

/-- The transition of a waiting state at the enabled signature reply. -/
theorem updateGotCode_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s) (h : G₁)
    (marks : List (Mark F)) (hml : marks.length ≤ cap) (m : K × F)
    (next : (generalSpec K (K × F) G₁ randomBound).Range (.inr m) → R.machine.State)
    (hv : R.machine.view s = .inr ⟨.inr m, next⟩) (σ : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx_def : idx = ⟨.inr m, σ⟩)
    (hupd : Q.cost R.updateCode (s, tagSign (m, σ + correction m • h)) ≤ work)
    (hs' : Q.size R.state (next (σ + correction m • h)) ≤ stateWidth) :
    Q.cost (updateGotCode rep data cost primitive ports wports correction finalFn keys code R) ((s, h, marks), idx) ≤
      2 * work + 2 * routineTime + 2 * opTime + 3 * adapterTime + 92 * tick := by
  have hreq := hs.request (.inr m) next hv
  have hmsg : Q.size msgRep m ≤ width := hreq
  have hh := S.fcaps.hdr
  have hHR := S.headRoute
  have hss := hs.state
  have hsh := hs.head
  have hσ := S.point₁ σ
  have hidx : Q.size bdI.idx idx ≤ 8 * width := by rw [hidx_def]; exact (S.pcaps.signTag m σ hmsg hσ).1
  have hnext : R.machine.update? (s, tagSign (m, σ + correction m • h)) = some (next (σ + correction m • h)) :=
    R.machine.update?_of_view_query hv _
  obtain ⟨hframe, hsctx, hctx, hgot⟩ := signFrame_sizes S s hss h marks hml m hmsg σ idx hidx
  have hout := pair_size S.sizes bdI.head (gotCtx rep R) (R.machine.head s) ((s, h, marks), idx) hsh le_rfl
  obtain ⟨hm0, -, -⟩ := marks_sizes S marks hml markHash
  have hhd : Q.size (prod bdI.head (gotCtx rep R)) (R.machine.head s, ((s, h, marks), idx)) ≤ WF :=
    (pair_size S.sizes bdI.head (gotCtx rep R) (R.machine.head s) ((s, h, marks), idx) hsh
      (pair_size S.sizes (gotRep rep R) bdI.idx (s, h, marks) idx
        (pair_size S.sizes R.state (prod pRep mRep) s (h, marks) hss (pair_size S.sizes pRep mRep h marks (S.point₁ h) hm0))
        hidx)).trans (by
        have h1 := S.fcaps.hdr
        have h2 := S.headRoute
        unfold wrapFrame at *
        omega)
  have hhead := R.machine.head_eq_inr_of_view hv
  have hhd' : Q.size (prod bdI.head (gotCtx rep R)) (.inr (.inr m), ((s, h, marks), idx)) ≤ WF := by
    rw [hhead] at hhd; exact hhd
  obtain ⟨-, hbd, hdec⟩ := pairRightRequest_cost S (gotCtx rep R) (.inr m) hreq ((s, h, marks), idx) (by sz)
  have hpctx := pair_size S.sizes bdI.pos (gotCtx rep R) (.inr m) ((s, h, marks), idx) hbd le_rfl
  have hdist := inr_size S.sizes (prod bdI.out (gotCtx rep R)) (prod bdI.pos (gotCtx rep R)) (.inr m, ((s, h, marks), idx)) le_rfl
  obtain ⟨hm, hm', hmark⟩ := marks_sizes S marks hml (markSign correction m)
  have hp' := pair_size S.sizes R.state mRep (next (σ + correction m • h)) (markSign correction m :: marks) hs' hm'
  have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI)))
    (next (σ + correction m • h), markSign correction m :: marks) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (ready R.machine (next (σ + correction m • h)) (markSign correction m :: marks)) le_rfl
  have hval : Q.size (opt (stateRep rep R))
      ((R.machine.update? (s, tagSign (m, σ + correction m • h))).map fun x => ready R.machine x (markSign correction m :: marks)) ≤
      WF := by
    rw [hnext]; sz
  have twith := withInputHeadGot_cost S s hs h marks hml idx hidx
  have treq := requestGotCode_cost S s hs h marks hml m ⟨next, hv⟩ σ idx hidx_def hupd _ hnext hs'
  subst hidx_def
  nz
  unfold updateGotCode
  apply CAST
  have d1 := DISTRIBUTE bdI.out bdI.pos (gotCtx rep R) (R.machine.head s, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound)))
    (by first | exact hhd | exact hhd' | ((try simp only [hhead]); szg)) (by (try simp only [hhead]); szg)
  rw [hhead] at d1
  have e1 := ELIMR (Q.compose (QuantitativeStepClass.HasProd.pairLeft Q QP (dropPointCode rep R))
      (finishReadyCode rep data cost primitive ports wports R)) _ (Sum.inr m, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))) treq
    (by szg) (by first | exact hval | szg)
  have c1 := COMPOSE _ _ (Sum.inr (Sum.inr m), ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))) d1 e1
    (by first | exact hhd | exact hhd' | szg) (by szg) (by first | exact hval | szg)
  have c2 : Q.cost (QuantitativeStepClass.IsDistributive.elimContext Q QD
      (Q.compose (QuantitativeStepClass.HasProd.pairLeft Q QP (dropPointCode rep R)) (finishReadyCode rep data cost primitive ports wports R))
      (requestGotCode rep data cost primitive ports wports correction finalFn keys code R)) (R.machine.head s, ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound))) ≤
      work + 2 * routineTime + 2 * opTime + 3 * adapterTime + 85 * tick := by
    unfold QuantitativeStepClass.IsDistributive.elimContext
    apply CAST
    rw [hhead]
    exact c1.trans (by szg)
  have := COMPOSE _ _ ((s, h, marks), (⟨.inr m, σ⟩ : GeneralIndex K (K × F) G₁ randomBound)) twith c2 (by szg)
    (by first | exact hhd | exact hhd' | ((try simp only [hhead]); szg))
    (by (try simp only [hhead]); first | exact hval | szg)
  sz

/-! ## The transition -/

/-- The transition at an enabled step of the wrapper: from a ready state, or from a waiting state
whose signature arrives. -/
theorem updateCode_cost (st : State R.machine (F := F)) (idx : GeneralIndex K (K × F) G₁ randomBound)
    (henabled :
      (∃ s marks, st = ready R.machine s marks ∧ InnerState rep width stateWidth headWidth work s ∧ marks.length ≤ cap ∧
        ((∃ result h, R.machine.view s = .inl result ∧ idx = ⟨.inl (.inr (finalIndex result)), h⟩) ∨
        (∃ (pos : GeneralRequest K (K × F) randomBound) (next : (generalSpec K (K × F) G₁ randomBound).Range pos → R.machine.State)
          (dir : (generalSpec K (K × F) G₁ randomBound).Range pos), R.machine.view s = .inr ⟨pos, next⟩ ∧
          pos.isLeft = true ∧ idx = ⟨pos, dir⟩ ∧ Q.cost R.updateCode (s, idx) ≤ work ∧
          Q.size R.state (next dir) ≤ stateWidth) ∨
        (∃ m next h, R.machine.view s = .inr ⟨.inr m, next⟩ ∧ idx = ⟨.inl (.inr m.1), h⟩))) ∨
      (∃ (s : R.machine.State) (h : G₁) (marks : List (Mark F)) (m : K × F)
        (next : (generalSpec K (K × F) G₁ randomBound).Range (.inr m) → R.machine.State) (σ : G₁),
        st = gotHash R.machine s h marks ∧ InnerState rep width stateWidth headWidth work s ∧ marks.length ≤ cap ∧
        R.machine.view s = .inr ⟨.inr m, next⟩ ∧ idx = ⟨.inr m, σ⟩ ∧
        Q.cost R.updateCode (s, tagSign (m, σ + correction m • h)) ≤ work ∧
        Q.size R.state (next (σ + correction m • h)) ≤ stateWidth)) :
    Q.cost (updateCode rep data cost primitive ports wports correction finalFn keys code R) (st, idx) ≤
      updateTime overhead width cap stateWidth routeWidth outputWidth finishedRoute adapterTime routineTime opTime comparisonTime
        work := by
  have hh := S.fcaps.hdr
  have hHR := S.headRoute
  rcases henabled with ⟨s, marks, rfl, hs, hml, hcase⟩ | ⟨s, h, marks, m, next, σ, rfl, hs, hml, hv, hidx_def, hupd, hs'⟩
  · have hidx : Q.size bdI.idx idx ≤ 8 * width := by
      rcases hcase with ⟨result, h, hv, rfl⟩ | ⟨pos, next, dir, hv, hleft, rfl, -, -⟩ | ⟨m, next, h, hv, rfl⟩
      · have hres := hs.output S result hv
        obtain ⟨hdec, -⟩ := S.wcaps.output result (hres.trans S.headRoute)
        exact (S.pcaps.hashTag _ h (outputKey_size S result hdec) (S.point₁ h)).1
      · have hreq := hs.request pos next hv
        rcases pos with (n | t) | m
        · exact (S.pcaps.randomTag ⟨n, dir⟩).1
        · exact (S.pcaps.hashTag t dir hreq (S.point₁ dir)).1
        · simp at hleft
      · have hreq := hs.request (.inr m) next hv
        exact (S.pcaps.hashTag m.1 h ((S.sizes.fst_le _ _ m).trans hreq) (S.point₁ h)).1
    obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
    have hready := pair_size S.sizes R.state mRep s marks hs.state hm
    have hctx := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
    have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s, marks) le_rfl
    have hsidx := pair_size S.sizes (stateRep rep R) bdI.idx (ready R.machine s marks) idx le_rfl hidx
    have hdist := inl_size S.sizes (readyCtx rep R) (prod (sum (gotRep rep R) (doneRep rep (bdI := bdI))) bdI.idx) ((s, marks), idx) le_rfl
    have tready := updateReadyCode_cost S s hs marks hml idx hcase
    -- the resulting optional state is a wrapper state in the frame
    have hres : Q.size (opt (stateRep rep R)) (updateReadyFn R s marks idx) + 16 * width ≤ WF := by
      rcases hcase with ⟨result, h, hv, rfl⟩ | ⟨pos, next, dir, hv, hleft, rfl, -, hs'⟩ | ⟨m, next, h, hv, rfl⟩
      · have hres := hs.output S result hv
        have hdone := pair_size S.sizes bdI.out mRep result marks hres hm
        have hin := inr_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (result, marks) le_rfl
        have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inr (result, marks)) le_rfl
        have hsome := some_size S.sizes (stateRep rep R) (done R.machine result marks) le_rfl
        simp only [updateReadyFn, R.machine.head_eq_inl_of_view hv, decodeIdx, ite_true]
        sz
      · obtain ⟨-, hm', -⟩ := marks_sizes S marks hml markHash
        have hp' := pair_size S.sizes R.state mRep (next dir) marks hs' hm
        have hp'' := pair_size S.sizes R.state mRep (next dir) (markHash :: marks) hs' hm'
        have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (next dir, marks) le_rfl
        have hin' := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (next dir, markHash :: marks) le_rfl
        have hsome := some_size S.sizes (stateRep rep R) (ready R.machine (next dir) marks) le_rfl
        have hsome' := some_size S.sizes (stateRep rep R) (ready R.machine (next dir) (markHash :: marks)) le_rfl
        have hnext := R.machine.update?_of_view_query hv dir
        rcases pos with (n | t) | m
        · simp only [updateReadyFn, R.machine.head_eq_inr_of_view hv, hnext, Option.map_some]; sz
        · simp only [updateReadyFn, R.machine.head_eq_inr_of_view hv, hnext, Option.map_some]; sz
        · simp at hleft
      · have hhm := pair_size S.sizes pRep mRep h marks (S.point₁ h) hm
        have hgot := pair_size S.sizes R.state (prod pRep mRep) s (h, marks) hs.state hhm
        have hin := inl_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (s, h, marks) le_rfl
        have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inl (s, h, marks)) le_rfl
        have hsome := some_size S.sizes (stateRep rep R) (gotHash R.machine s h marks) le_rfl
        simp only [updateReadyFn, R.machine.head_eq_inr_of_view hv, decodeIdx, ite_true]
        sz
    have hfn := congrFun (updateFn_eq correction finalFn keys R) (ready R.machine s marks, idx)
    nz
    unfold updateCode
    apply CAST
    have d1 := DISTRIBUTE (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) bdI.idx (Sum.inl (s, marks), idx)
      (by szg) (by szg)
    have e1 := ELIML _ (Q.compose (QD.distribute (gotRep rep R) (doneRep rep (bdI := bdI)) bdI.idx)
        (QS.elim (updateGotCode rep data cost primitive ports wports correction finalFn keys code R)
          (QO.none (prod (doneRep rep (bdI := bdI)) bdI.idx) (stateRep rep R)))) ((s, marks), idx) tready (by szg)
      (by change Q.size (opt (stateRep rep R)) (updateReadyFn R s marks idx) ≤ _; szg)
    have := COMPOSE _ _ (Sum.inl (s, marks), idx) d1 e1 (by szg) (by szg)
      (by change Q.size (opt (stateRep rep R)) (updateReadyFn R s marks idx) ≤ _; szg)
    unfold updateTime readyTime at *
    sz
  · have hreq := hs.request (.inr m) next hv
    have hmsg : Q.size msgRep m ≤ width := hreq
    have hσ := S.point₁ σ
    have hidx : Q.size bdI.idx idx ≤ 8 * width := by rw [hidx_def]; exact (S.pcaps.signTag m σ hmsg hσ).1
    obtain ⟨hframe, hsctx, hctx, hgot⟩ := signFrame_sizes S s hs.state h marks hml m hmsg σ idx hidx
    have hin := inl_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (s, h, marks) le_rfl
    have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inl (s, h, marks)) le_rfl
    have hsidx := pair_size S.sizes (stateRep rep R) bdI.idx (gotHash R.machine s h marks) idx le_rfl hidx
    have hgidx := pair_size S.sizes (sum (gotRep rep R) (doneRep rep (bdI := bdI))) bdI.idx (.inl (s, h, marks)) idx le_rfl hidx
    have hdist := inr_size S.sizes (readyCtx rep R) (prod (sum (gotRep rep R) (doneRep rep (bdI := bdI))) bdI.idx)
      (.inl (s, h, marks), idx) le_rfl
    have hdist' := inl_size S.sizes (gotCtx rep R) (prod (doneRep rep (bdI := bdI)) bdI.idx) ((s, h, marks), idx) le_rfl
    obtain ⟨hm, hm', hmark⟩ := marks_sizes S marks hml (markSign correction m)
    have hp' := pair_size S.sizes R.state mRep (next (σ + correction m • h)) (markSign correction m :: marks) hs' hm'
    have hinr := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI)))
      (next (σ + correction m • h), markSign correction m :: marks) le_rfl
    have hsome := some_size S.sizes (stateRep rep R) (ready R.machine (next (σ + correction m • h)) (markSign correction m :: marks)) le_rfl
    have hnext := R.machine.update?_of_view_query hv (σ + correction m • h)
    have tgot := updateGotCode_cost S s hs h marks hml m next hv σ idx hidx_def hupd hs'
    have hres : Q.size (opt (stateRep rep R)) (updateGotFn correction R s h marks idx) + 16 * width ≤ WF := by
      subst hidx_def
      simp only [updateGotFn, R.machine.head_eq_inr_of_view hv, decodeIdx, tagSign, hnext, Option.map_some]
      sz
    have hfn := congrFun (updateFn_eq correction finalFn keys R) (gotHash R.machine s h marks, idx)
    nz
    unfold updateCode
    apply CAST
    have d1 := DISTRIBUTE (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) bdI.idx
      (Sum.inr (Sum.inl (s, h, marks)), idx) (by szg) (by szg)
    have d2 := DISTRIBUTE (gotRep rep R) (doneRep rep (bdI := bdI)) bdI.idx (Sum.inl (s, h, marks), idx) (by szg) (by szg)
    have e2 := ELIML _ (QO.none (prod (doneRep rep (bdI := bdI)) bdI.idx) (stateRep rep R)) ((s, h, marks), idx) tgot (by szg)
      (by change Q.size (opt (stateRep rep R)) (updateGotFn correction R s h marks idx) ≤ _; szg)
    have c2 := COMPOSE _ _ (Sum.inl (s, h, marks), idx) d2 e2 (by szg) (by szg)
      (by change Q.size (opt (stateRep rep R)) (updateGotFn correction R s h marks idx) ≤ _; szg)
    have e1 := ELIMR (updateReadyCode rep data cost primitive ports wports R) _ (Sum.inl (s, h, marks), idx) c2 (by szg)
      (by change Q.size (opt (stateRep rep R)) (updateGotFn correction R s h marks idx) ≤ _; szg)
    have := COMPOSE _ _ (Sum.inr (Sum.inl (s, h, marks)), idx) d1 e1 (by szg) (by szg)
      (by change Q.size (opt (stateRep rep R)) (updateGotFn correction R s h marks idx) ≤ _; szg)
    unfold updateTime at *
    sz

end Signatures.Runtime.SyncWrapGeneral
