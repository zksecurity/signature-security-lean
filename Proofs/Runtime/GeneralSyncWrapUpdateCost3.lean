import Proofs.Runtime.GeneralSyncWrapUpdateCost2

/-! # Cost of the wrapper's transition, part three: the ready dispatch

The pending request of the attacker selects the continuation: a random or hash reply is fed back
with the mark recorded, a signing request makes the wrapper hold the period's hash. -/

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



/-! ## Dispatching the attacker's pending request -/

/-- Reading the pending request alongside its context. -/
theorem pairRightRequest_cost {E : Type} (e : C.Str E) (pos : GeneralRequest K (K × F) randomBound)
    (hpos : WeightedAGM.NativeHandler.RequestSized (Q := Q) rep key Weights.syncMessage width pos)
    (ctx : E) (hctx : Q.size e ctx + 16 * width ≤ WF) :
    Q.cost (QuantitativeStepClass.HasProd.pairRight Q QP (d := e) ports.request) (pos, ctx) ≤ adapterTime + 4 * tick ∧
      Q.size bdI.pos pos ≤ 8 * width ∧ Q.size (posRep rep) pos ≤ 3 * width := by
  have hh := S.fcaps.hdr
  obtain ⟨hbd, treq⟩ := S.pcaps.request pos hpos
  have hdec : Q.size (posRep rep) pos ≤ 3 * width :=
    WeightedAGM.NativeHandler.request_size rep key Weights.syncMessage S.sizes width hh pos hpos
  have hin := pair_size S.sizes bdI.pos e pos ctx hbd le_rfl
  have hout := pair_size S.sizes (posRep rep) e pos ctx hdec le_rfl
  refine ⟨?_, hbd, hdec⟩
  nz
  unfold QuantitativeStepClass.HasProd.pairRight
  apply CAST
  have a1 := FST bdI.pos e (pos, ctx) (by szg) (by szg)
  have a2 := COMPOSE _ _ (pos, ctx) a1 treq (by szg) (by szg) (by szg)
  have a3 := SND bdI.pos e (pos, ctx) (by szg) (by szg)
  have := PAIR _ _ (pos, ctx) a2 a3 (by szg) (by szg)
  sz

/-- The budget of the transition at any enabled step. -/
def updateTime (overhead : Nat → Nat) (width cap stateWidth routeWidth outputWidth finishedRoute adapterTime routineTime
    opTime comparisonTime work : Nat) : Nat :=
  2 * work + 2 * routineTime + 2 * opTime + 3 * adapterTime + comparisonTime +
    98 * fee overhead (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)

/-- The continuation on a random or hash reply, with the attacker's enabled update. -/
theorem requestReady_continue_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s)
    (marks : List (Mark F)) (hml : marks.length ≤ cap) (pos : GeneralRequest K (K × F) randomBound)
    (hv : ∃ next, R.machine.view s = .inr ⟨pos, next⟩) (idx : GeneralIndex K (K × F) G₁ randomBound)
    (hidx : Q.size bdI.idx idx ≤ 8 * width) (hupd : Q.cost R.updateCode (s, idx) ≤ work)
    (s' : R.machine.State) (hnext : R.machine.update? (s, idx) = some s') (hs' : Q.size R.state s' ≤ stateWidth)
    (hpos : pos.isLeft = true) :
    Q.cost (requestReadyCode rep data cost primitive ports wports R) (pos, ((s, marks), idx)) ≤
      work + adapterTime + opTime + 37 * tick := by
  obtain ⟨next, hv⟩ := hv
  have hreq := hs.request pos next hv
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  obtain ⟨hm, hm', -⟩ := marks_sizes S marks hml markHash
  have hready := pair_size S.sizes R.state mRep s marks hs.state hm
  have hctx := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  obtain ⟨tpr, hbd, hdec⟩ := pairRightRequest_cost S (readyCtx rep R) pos hreq ((s, marks), idx) (by sz)
  have hposctx := pair_size S.sizes (posRep rep) (readyCtx rep R) pos ((s, marks), idx) hdec le_rfl
  have hbdctx := pair_size S.sizes bdI.pos (readyCtx rep R) pos ((s, marks), idx) hbd le_rfl
  have hres : Q.size (opt R.state) (R.machine.update? (s, idx)) ≤ stateWidth + header := by
    rw [hnext]; exact some_size S.sizes R.state s' hs'
  have hp' := pair_size S.sizes R.state mRep s' marks hs' hm
  have hp'' := pair_size S.sizes R.state mRep s' (markHash :: marks) hs' hm'
  have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s', marks) le_rfl
  have hin' := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s', markHash :: marks) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (ready R.machine s' marks) le_rfl
  have hsome' := some_size S.sizes (stateRep rep R) (ready R.machine s' (markHash :: marks)) le_rfl
  have hval : Q.size (opt (stateRep rep R)) ((R.machine.update? (s, idx)).map fun x => ready R.machine x marks) ≤ WF := by
    rw [hnext]; sz
  have hval' : Q.size (opt (stateRep rep R)) ((R.machine.update? (s, idx)).map fun x => ready R.machine x (markHash :: marks)) ≤
      WF := by
    rw [hnext]; sz
  have tkeep := stepReadyCode_cost S (keepMarksCode rep) s hs.state marks hml (by omega)
    (keepMarksCode_cost S marks hml) idx hidx hupd s' hnext hs'
  have trecord := stepReadyCode_cost S (recordHashCode rep data cost primitive) s hs.state marks hml (by simp; omega)
    (recordHashCode_cost S marks hml) idx hidx hupd s' hnext hs'
  nz
  unfold requestReadyCode
  apply CAST
  rcases pos with (n | t) | m
  · -- a random reply
    have hl : Q.size (sum boundedRep kRep) (Sum.inl n) ≤ 3 * width := inl_payload S.sizes _ _ _ hdec
    have hn : Q.size boundedRep n ≤ 3 * width := inl_payload S.sizes _ _ _ hl
    have hnctx := pair_size S.sizes boundedRep (readyCtx rep R) n ((s, marks), idx) hn le_rfl
    have hlctx := pair_size S.sizes (sum boundedRep kRep) (readyCtx rep R) (Sum.inl n) ((s, marks), idx) hl le_rfl
    have hdist1 := inl_size S.sizes (prod (sum boundedRep kRep) (readyCtx rep R)) (prod msgRep (readyCtx rep R))
      (Sum.inl n, ((s, marks), idx)) le_rfl
    have hdist2 := inl_size S.sizes (prod boundedRep (readyCtx rep R)) (prod kRep (readyCtx rep R)) (n, ((s, marks), idx)) le_rfl
    nz
    have a1 := SND boundedRep (readyCtx rep R) (n, ((s, marks), idx)) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg)
    have a2 := COMPOSE _ _ (n, ((s, marks), idx)) a1 tkeep (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg) (by (try dsimp only); (try simp only [hnext]); szg)
    have a3 := DISTRIBUTE boundedRep kRep (readyCtx rep R) (Sum.inl n, ((s, marks), idx)) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg)
    have a4 := ELIML _ (Q.compose (QP.snd kRep (readyCtx rep R)) (stepReadyCode rep R (recordHashCode rep data cost primitive)))
      (n, ((s, marks), idx)) a2 (by first | exact hval | exact hval' | szg) (by exact hval)
    have a5 := COMPOSE _ _ (Sum.inl n, ((s, marks), idx)) a3 a4 (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg) (by exact hval)
    have a6 := DISTRIBUTE (sum boundedRep kRep) msgRep (readyCtx rep R) (Sum.inl (Sum.inl n), ((s, marks), idx)) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg)
    exact le_trans (COMPOSE _ _ (Sum.inl (Sum.inl n), ((s, marks), idx)) tpr
      (le_trans (CAST _ _ _ (COMPOSE _ _ (Sum.inl (Sum.inl n), ((s, marks), idx)) a6
        (ELIML _ (holdHashCode rep data cost primitive ports wports R) (Sum.inl n, ((s, marks), idx))
          (CAST _ _ _ a5) (by first | exact hval | exact hval' | szg) (by exact hval)) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg) (by exact hval))) le_rfl)
      (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg) (by exact hval)) (by first | exact hval | exact hval' | szg)
  · -- a hash reply
    have hl : Q.size (sum boundedRep kRep) (Sum.inr t) ≤ 3 * width := inl_payload S.sizes _ _ _ hdec
    have ht : Q.size kRep t ≤ 3 * width := inr_payload S.sizes _ _ _ hl
    have htctx := pair_size S.sizes kRep (readyCtx rep R) t ((s, marks), idx) ht le_rfl
    have hlctx := pair_size S.sizes (sum boundedRep kRep) (readyCtx rep R) (Sum.inr t) ((s, marks), idx) hl le_rfl
    have hdist1 := inl_size S.sizes (prod (sum boundedRep kRep) (readyCtx rep R)) (prod msgRep (readyCtx rep R))
      (Sum.inr t, ((s, marks), idx)) le_rfl
    have hdist2 := inr_size S.sizes (prod boundedRep (readyCtx rep R)) (prod kRep (readyCtx rep R)) (t, ((s, marks), idx)) le_rfl
    nz
    have a1 := SND kRep (readyCtx rep R) (t, ((s, marks), idx)) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg)
    have a2 := COMPOSE _ _ (t, ((s, marks), idx)) a1 trecord (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval')
    have a3 := DISTRIBUTE boundedRep kRep (readyCtx rep R) (Sum.inr t, ((s, marks), idx)) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg)
    have a4 := ELIMR (Q.compose (QP.snd boundedRep (readyCtx rep R)) (stepReadyCode rep R (keepMarksCode rep))) _
      (t, ((s, marks), idx)) a2 (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval')
    have a5 := COMPOSE _ _ (Sum.inr t, ((s, marks), idx)) a3 a4 (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval')
    have a6 := DISTRIBUTE (sum boundedRep kRep) msgRep (readyCtx rep R) (Sum.inl (Sum.inr t), ((s, marks), idx)) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg)
    exact le_trans (COMPOSE _ _ (Sum.inl (Sum.inr t), ((s, marks), idx)) tpr
      (le_trans (CAST _ _ _ (COMPOSE _ _ (Sum.inl (Sum.inr t), ((s, marks), idx)) a6
        (ELIML _ (holdHashCode rep data cost primitive ports wports R) (Sum.inr t, ((s, marks), idx))
          (CAST _ _ _ a5) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval')) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval'))) le_rfl)
      (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval' | szg) (by first | exact hval | exact hval')) (by first | exact hval | exact hval' | szg)
  · simp at hpos

/-- The hold on a signing request. -/
theorem requestReady_sign_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s)
    (marks : List (Mark F)) (hml : marks.length ≤ cap) (m : K × F)
    (hv : ∃ next, R.machine.view s = .inr ⟨.inr m, next⟩) (h : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx_def : idx = ⟨.inl (.inr m.1), h⟩) :
    Q.cost (requestReadyCode rep data cost primitive ports wports R) (.inr m, ((s, marks), idx)) ≤
      2 * adapterTime + comparisonTime + 62 * tick := by
  obtain ⟨next, hv⟩ := hv
  have hreq := hs.request _ next hv
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hmsg : Q.size msgRep m ≤ width := hreq
  have hkey : Q.size kRep m.1 ≤ Q.size msgRep m := S.sizes.fst_le _ _ m
  have hpt := S.point₁ h
  have hidx : Q.size bdI.idx idx ≤ 8 * width := by
    rw [hidx_def]; exact (S.pcaps.hashTag m.1 h (by omega) hpt).1
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hready := pair_size S.sizes R.state mRep s marks hs.state hm
  have hctx := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  obtain ⟨tpr, hbd, hdec⟩ := pairRightRequest_cost S (readyCtx rep R) (.inr m) hreq ((s, marks), idx) (by sz)
  have hposctx := pair_size S.sizes (posRep rep) (readyCtx rep R) (.inr m) ((s, marks), idx) hdec le_rfl
  have hbdctx := pair_size S.sizes bdI.pos (readyCtx rep R) (.inr m) ((s, marks), idx) hbd le_rfl
  have hmctx := pair_size S.sizes msgRep (readyCtx rep R) m ((s, marks), idx) hmsg le_rfl
  have hdist := inr_size S.sizes (prod (sum boundedRep kRep) (readyCtx rep R)) (prod msgRep (readyCtx rep R))
    (m, ((s, marks), idx)) le_rfl
  have hhm := pair_size S.sizes pRep mRep h marks hpt hm
  have hgot := pair_size S.sizes R.state (prod pRep mRep) s (h, marks) hs.state hhm
  have hin := inl_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (s, h, marks) le_rfl
  have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inl (s, h, marks)) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (gotHash R.machine s h marks) le_rfl
  have thold := holdHashCode_cost S s hs.state marks hml m hmsg h idx hidx_def hidx
  subst hidx_def
  nz
  unfold requestReadyCode
  apply CAST
  have a6 := DISTRIBUTE (sum boundedRep kRep) msgRep (readyCtx rep R) (Sum.inr m, ((s, marks), (⟨.inl (.inr m.1), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) (by szg) (by szg)
  exact le_trans (COMPOSE _ _ (Sum.inr m, ((s, marks), (⟨.inl (.inr m.1), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) tpr
    (le_trans (CAST _ _ _ (COMPOSE _ _ (Sum.inr m, ((s, marks), (⟨.inl (.inr m.1), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) a6
      (ELIMR _ (holdHashCode rep data cost primitive ports wports R) (m, ((s, marks), (⟨.inl (.inr m.1), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) thold (by szg) (by szg))
      (by szg) (by szg) (by szg))) le_rfl)
    (by szg) (by szg) (by szg)) (by szg)

end Signatures.Runtime.SyncWrapGeneral
