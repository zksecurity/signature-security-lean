import Proofs.Runtime.GeneralSyncWrapUpdateCost3

/-! # Cost of the wrapper's transition, part four: the ready state

The transition from a ready state reads the attacker's readout once and dispatches: a returned
forgery meets its final hash, an own request meets its reply, a signing request meets the
period's hash. -/

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




/-! ## The transition from a ready state -/

/-- Reading the attacker's readout while retaining the context. -/
theorem withInputHead_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s)
    (marks : List (Mark F)) (hml : marks.length ≤ cap) (idx : GeneralIndex K (K × F) G₁ randomBound)
    (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.cost (QuantitativeStepClass.HasProd.withInput Q QP
      (Q.compose (QP.fst (readyRep rep R) bdI.idx) (Q.compose (QP.fst R.state mRep) R.headCode))) ((s, marks), idx) ≤
      work + 6 * tick := by
  have hh := S.fcaps.hdr
  have hHR := S.headRoute
  have hss := hs.state
  have hsh := hs.head
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hready := pair_size S.sizes R.state mRep s marks hss hm
  have hctx := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  have hout := pair_size S.sizes bdI.head (readyCtx rep R) (R.machine.head s) ((s, marks), idx) hsh le_rfl
  nz
  unfold QuantitativeStepClass.HasProd.withInput
  have a1 := FST (readyRep rep R) bdI.idx ((s, marks), idx) (by szg) (by szg)
  have a2 := FST R.state mRep (s, marks) (by szg) (by szg)
  have a3 := COMPOSE _ _ (s, marks) a2 hs.headCost (by szg) (by szg) (by szg)
  have a4 := COMPOSE _ _ ((s, marks), idx) a1 a3 (by szg) (by szg) (by szg)
  have a5 := IDENT (readyCtx rep R) ((s, marks), idx) (by szg)
  have := PAIR _ _ ((s, marks), idx) a4 a5 (by szg) (by szg)
  sz

/-- The transition budget from a ready state, before the outer dispatch. -/
def readyTime (overhead : Nat → Nat) (width cap stateWidth routeWidth outputWidth finishedRoute adapterTime opTime
    comparisonTime work : Nat) : Nat :=
  2 * work + 2 * adapterTime + comparisonTime + opTime +
    72 * fee overhead (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)

/-- The transition of a ready state at an enabled reply: the attacker returned and the final hash
arrives, or the attacker's own request is answered, or it asked to sign and the period's hash
arrives. -/
theorem updateReadyCode_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s)
    (marks : List (Mark F)) (hml : marks.length ≤ cap) (idx : GeneralIndex K (K × F) G₁ randomBound)
    (henabled :
      (∃ result h, R.machine.view s = .inl result ∧ idx = ⟨.inl (.inr (finalIndex result)), h⟩) ∨
      (∃ (pos : GeneralRequest K (K × F) randomBound) (next : (generalSpec K (K × F) G₁ randomBound).Range pos → R.machine.State)
        (dir : (generalSpec K (K × F) G₁ randomBound).Range pos), R.machine.view s = .inr ⟨pos, next⟩ ∧
        pos.isLeft = true ∧ idx = ⟨pos, dir⟩ ∧ Q.cost R.updateCode (s, idx) ≤ work ∧
        Q.size R.state (next dir) ≤ stateWidth) ∨
      (∃ m next h, R.machine.view s = .inr ⟨.inr m, next⟩ ∧ idx = ⟨.inl (.inr m.1), h⟩)) :
    Q.cost (updateReadyCode rep data cost primitive ports wports R) ((s, marks), idx) ≤
      readyTime overhead width cap stateWidth routeWidth outputWidth finishedRoute adapterTime opTime comparisonTime work := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hss := hs.state
  have hsh := hs.head
  obtain ⟨hm, hm', -⟩ := marks_sizes S marks hml markHash
  have hready := pair_size S.sizes R.state mRep s marks hss hm
  rcases henabled with ⟨result, h, hv, hidx_def⟩ | ⟨pos, next, dir, hv, hleft, hidx_def, hupd, hs'⟩ | ⟨m, next, h, hv, hidx_def⟩
  · -- the final hash
    have hres := hs.output S result hv
    obtain ⟨hdec, -⟩ := S.wcaps.output result (hres.trans S.headRoute)
    have hkey := outputKey_size S result hdec
    have hidx : Q.size bdI.idx idx ≤ 8 * width := by
      rw [hidx_def]; exact (S.pcaps.hashTag _ h hkey (S.point₁ h)).1
    have hctx := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
    have hout := pair_size S.sizes bdI.head (readyCtx rep R) (R.machine.head s) ((s, marks), idx) hsh le_rfl
    have hhead := R.machine.head_eq_inl_of_view hv
    rw [hhead] at hsh hout
    have hrctx := pair_size S.sizes bdI.out (readyCtx rep R) result ((s, marks), idx) hres le_rfl
    have hdist := inl_size S.sizes (prod bdI.out (readyCtx rep R)) (prod bdI.pos (readyCtx rep R)) (result, ((s, marks), idx)) le_rfl
    have hdone := pair_size S.sizes bdI.out mRep result marks hres hm
    have hin := inr_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (result, marks) le_rfl
    have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inr (result, marks)) le_rfl
    have hsome := some_size S.sizes (stateRep rep R) (done R.machine result marks) le_rfl
    have twith := withInputHead_cost S s hs marks hml idx hidx
    have tfin := finishReadyCode_cost S s hss marks hml result hres h idx hidx_def hidx
    subst hidx_def
    nz
    unfold updateReadyCode
    apply CAST
    have d1 := DISTRIBUTE bdI.out bdI.pos (readyCtx rep R) (R.machine.head s, ((s, marks), (⟨.inl (.inr (finalIndex result)), h⟩ : GeneralIndex K (K × F) G₁ randomBound)))
      (by (try simp only [hhead]); szg) (by (try simp only [hhead]); szg)
    rw [hhead] at d1
    have e1 := ELIML _ (requestReadyCode rep data cost primitive ports wports R) (result, ((s, marks), (⟨.inl (.inr (finalIndex result)), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) tfin
      (by (try simp only [hhead]); szg) (by (try simp only [hhead]); szg)
    have c1 := COMPOSE _ _ (Sum.inl result, ((s, marks), (⟨.inl (.inr (finalIndex result)), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) d1 e1 (by szg) (by szg) (by szg)
    have c2 : Q.cost (QuantitativeStepClass.IsDistributive.elimContext Q QD (finishReadyCode rep data cost primitive ports wports R)
        (requestReadyCode rep data cost primitive ports wports R)) (R.machine.head s, ((s, marks), (⟨.inl (.inr (finalIndex result)), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) ≤
        2 * adapterTime + comparisonTime + 52 * tick := by
      unfold QuantitativeStepClass.IsDistributive.elimContext
      apply CAST
      rw [hhead]
      exact c1.trans (by szg)
    have := COMPOSE _ _ ((s, marks), (⟨.inl (.inr (finalIndex result)), h⟩ : GeneralIndex K (K × F) G₁ randomBound)) twith c2 (by szg) (by (try simp only [hhead]); szg)
      (by (try simp only [hhead]); szg)
    unfold readyTime
    sz
  · -- the attacker's own request is answered
    have hreq := hs.request pos next hv
    have hidx : Q.size bdI.idx idx ≤ 8 * width := by
      rw [hidx_def]
      rcases pos with (n | t) | m
      · exact (S.pcaps.randomTag ⟨n, dir⟩).1
      · exact (S.pcaps.hashTag t dir hreq (S.point₁ dir)).1
      · simp at hleft
    have hnext : R.machine.update? (s, idx) = some (next dir) := by
      rw [hidx_def]; exact R.machine.update?_of_view_query hv dir
    have hctx := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
    have hout := pair_size S.sizes bdI.head (readyCtx rep R) (R.machine.head s) ((s, marks), idx) hsh le_rfl
    have hhead := R.machine.head_eq_inr_of_view hv
    rw [hhead] at hsh hout
    obtain ⟨-, hbd, hdec⟩ := pairRightRequest_cost S (readyCtx rep R) pos hreq ((s, marks), idx) (by sz)
    have hpctx := pair_size S.sizes bdI.pos (readyCtx rep R) pos ((s, marks), idx) hbd le_rfl
    have hdist := inr_size S.sizes (prod bdI.out (readyCtx rep R)) (prod bdI.pos (readyCtx rep R)) (pos, ((s, marks), idx)) le_rfl
    have twith := withInputHead_cost S s hs marks hml idx hidx
    have treq := requestReady_continue_cost S s hs marks hml pos ⟨next, hv⟩ idx hidx hupd (next dir) hnext hs' hleft
    have hp' := pair_size S.sizes R.state mRep (next dir) marks hs' hm
    have hp'' := pair_size S.sizes R.state mRep (next dir) (markHash :: marks) hs' hm'
    have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (next dir, marks) le_rfl
    have hin' := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (next dir, markHash :: marks) le_rfl
    have hsome := some_size S.sizes (stateRep rep R) (ready R.machine (next dir) marks) le_rfl
    have hsome' := some_size S.sizes (stateRep rep R) (ready R.machine (next dir) (markHash :: marks)) le_rfl
    have hval : Q.size (opt (stateRep rep R)) ((R.machine.update? (s, idx)).map fun x => ready R.machine x marks) ≤ WF := by
      rw [hnext]; sz
    have hval' : Q.size (opt (stateRep rep R)) ((R.machine.update? (s, idx)).map fun x => ready R.machine x (markHash :: marks)) ≤
        WF := by
      rw [hnext]; sz
    nz
    unfold updateReadyCode
    apply CAST
    have d1 := DISTRIBUTE bdI.out bdI.pos (readyCtx rep R) (R.machine.head s, ((s, marks), idx))
      (by (try simp only [hhead]); szg) (by (try simp only [hhead]); szg)
    rw [hhead] at d1
    have e1 := ELIMR (finishReadyCode rep data cost primitive ports wports R) _ (pos, ((s, marks), idx)) treq
      (by szg) (by rcases pos with (n | t) | m <;> first | exact hval | exact hval' | simp at hleft)
    have c1 := COMPOSE _ _ (Sum.inr pos, ((s, marks), idx)) d1 e1 (by szg) (by szg)
      (by rcases pos with (n | t) | m <;> first | exact hval | exact hval' | simp at hleft)
    have c2 : Q.cost (QuantitativeStepClass.IsDistributive.elimContext Q QD (finishReadyCode rep data cost primitive ports wports R)
        (requestReadyCode rep data cost primitive ports wports R)) (R.machine.head s, ((s, marks), idx)) ≤
        work + adapterTime + opTime + 40 * tick := by
      unfold QuantitativeStepClass.IsDistributive.elimContext
      apply CAST
      rw [hhead]
      exact c1.trans (by szg)
    have := COMPOSE _ _ ((s, marks), idx) twith c2 (by szg) (by (try simp only [hhead]); szg)
      (by (try simp only [hhead]); rcases pos with (n | t) | m <;> first | exact hval | exact hval' | simp at hleft)
    unfold readyTime
    sz
  · -- a signing request: the period's hash arrives
    have hreq := hs.request _ next hv
    have hmsg : Q.size msgRep m ≤ width := hreq
    have hkey : Q.size kRep m.1 ≤ Q.size msgRep m := S.sizes.fst_le _ _ m
    have hidx : Q.size bdI.idx idx ≤ 8 * width := by
      rw [hidx_def]; exact (S.pcaps.hashTag m.1 h (by omega) (S.point₁ h)).1
    have hctx := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
    have hout := pair_size S.sizes bdI.head (readyCtx rep R) (R.machine.head s) ((s, marks), idx) hsh le_rfl
    have hhead := R.machine.head_eq_inr_of_view hv
    rw [hhead] at hsh hout
    obtain ⟨-, hbd, hdec⟩ := pairRightRequest_cost S (readyCtx rep R) (.inr m) hreq ((s, marks), idx) (by sz)
    have hpctx := pair_size S.sizes bdI.pos (readyCtx rep R) (.inr m) ((s, marks), idx) hbd le_rfl
    have hdist := inr_size S.sizes (prod bdI.out (readyCtx rep R)) (prod bdI.pos (readyCtx rep R)) (.inr m, ((s, marks), idx)) le_rfl
    have hhm := pair_size S.sizes pRep mRep h marks (S.point₁ h) hm
    have hgot := pair_size S.sizes R.state (prod pRep mRep) s (h, marks) hss hhm
    have hin := inl_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (s, h, marks) le_rfl
    have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inl (s, h, marks)) le_rfl
    have hsome := some_size S.sizes (stateRep rep R) (gotHash R.machine s h marks) le_rfl
    have twith := withInputHead_cost S s hs marks hml idx hidx
    have treq := requestReady_sign_cost S s hs marks hml m ⟨next, hv⟩ h idx hidx_def
    subst hidx_def
    nz
    unfold updateReadyCode
    apply CAST
    have d1 := DISTRIBUTE bdI.out bdI.pos (readyCtx rep R) (R.machine.head s, ((s, marks), (⟨.inl (.inr m.1), h⟩ : GeneralIndex K (K × F) G₁ randomBound)))
      (by (try simp only [hhead]); szg) (by (try simp only [hhead]); szg)
    rw [hhead] at d1
    have e1 := ELIMR (finishReadyCode rep data cost primitive ports wports R) _ (Sum.inr m, ((s, marks), (⟨.inl (.inr m.1), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) treq
      (by szg) (by szg)
    have c1 := COMPOSE _ _ (Sum.inr (Sum.inr m), ((s, marks), (⟨.inl (.inr m.1), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) d1 e1 (by szg) (by szg) (by szg)
    have c2 : Q.cost (QuantitativeStepClass.IsDistributive.elimContext Q QD (finishReadyCode rep data cost primitive ports wports R)
        (requestReadyCode rep data cost primitive ports wports R)) (R.machine.head s, ((s, marks), (⟨.inl (.inr m.1), h⟩ : GeneralIndex K (K × F) G₁ randomBound))) ≤
        2 * adapterTime + comparisonTime + 65 * tick := by
      unfold QuantitativeStepClass.IsDistributive.elimContext
      apply CAST
      rw [hhead]
      exact c1.trans (by szg)
    have := COMPOSE _ _ ((s, marks), (⟨.inl (.inr m.1), h⟩ : GeneralIndex K (K × F) G₁ randomBound)) twith c2 (by szg) (by (try simp only [hhead]); szg)
      (by (try simp only [hhead]); szg)
    unfold readyTime
    sz

end Signatures.Runtime.SyncWrapGeneral
