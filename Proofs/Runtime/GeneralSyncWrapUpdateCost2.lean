import Proofs.Runtime.GeneralSyncWrapUpdateCost

/-! # Cost of the wrapper's transition, part two: waiting for hashes

From a ready state the wrapper either continues the attacker on its own reply or, on a signing
request or a returned forgery, waits for one hash: the period's or the forgery's. -/

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


/-! ## Waiting for the final hash, holding a period's hash -/

theorem finishExpectedCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hr : Q.size bdI.out result ≤ headWidth)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.cost (finishExpectedCode rep ports wports R) (result, ((s, marks), idx)) ≤ adapterTime + 6 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  obtain ⟨hdec, hout⟩ := S.wcaps.output result (hr.trans S.headRoute)
  have hkey := outputKey_size S result hdec
  have hready := pair_size S.sizes R.state mRep s marks hs hm
  have hctx1 := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  have hctx := pair_size S.sizes bdI.out (readyCtx rep R) result ((s, marks), idx) hr le_rfl
  have tp := periodCode_cost S result hdec
  nz
  unfold finishExpectedCode
  apply CAST
  have a1 := FST bdI.out (readyCtx rep R) (result, ((s, marks), idx)) (by szg) (by szg)
  have a3 := COMPOSE _ _ result hout tp (by szg) (by szg) (by szg)
  have := COMPOSE _ _ (result, ((s, marks), idx)) a1 a3 (by szg) (by szg) (by szg)
  sz

theorem finishNextCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hr : Q.size bdI.out result ≤ headWidth)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width) (t : K)
    (ht : Q.size kRep t ≤ 8 * width) (h : G₁) :
    Q.cost (finishNextCode rep R) ((t, h), (result, ((s, marks), idx))) ≤ 15 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hpt := S.point₁ h
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hready := pair_size S.sizes R.state mRep s marks hs hm
  have hctx1 := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  have hctx := pair_size S.sizes bdI.out (readyCtx rep R) result ((s, marks), idx) hr le_rfl
  have hth := pair_size S.sizes kRep pRep t h ht hpt
  have hpair := pair_size S.sizes (prod kRep pRep) (prod bdI.out (readyCtx rep R)) (t, h) (result, ((s, marks), idx)) le_rfl le_rfl
  have hdone := pair_size S.sizes bdI.out mRep result marks hr hm
  have hin := inr_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (result, marks) le_rfl
  have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inr (result, marks)) le_rfl
  nz
  unfold finishNextCode
  apply CAST
  have a1 := SND (prod kRep pRep) (prod bdI.out (readyCtx rep R)) ((t, h), (result, ((s, marks), idx))) (by szg) (by szg)
  have a2 := FST bdI.out (readyCtx rep R) (result, ((s, marks), idx)) (by szg) (by szg)
  have a3 := COMPOSE _ _ ((t, h), (result, ((s, marks), idx))) a1 a2 (by szg) (by szg) (by szg)
  have a4 := SND bdI.out (readyCtx rep R) (result, ((s, marks), idx)) (by szg) (by szg)
  have a5 := FST (readyRep rep R) bdI.idx ((s, marks), idx) (by szg) (by szg)
  have a6 := SND R.state mRep (s, marks) (by szg) (by szg)
  have a7 := COMPOSE _ _ ((s, marks), idx) a5 a6 (by szg) (by szg) (by szg)
  have a8 := COMPOSE _ _ (result, ((s, marks), idx)) a4 a7 (by szg) (by szg) (by szg)
  have a9 := COMPOSE _ _ ((t, h), (result, ((s, marks), idx))) a1 a8 (by szg) (by szg) (by szg)
  have a10 := PAIR _ _ ((t, h), (result, ((s, marks), idx))) a3 a9 (by szg) (by szg)
  have a11 := INR (gotRep rep R) (doneRep rep (bdI := bdI)) (result, marks) (by szg) (by szg)
  have a12 := INR (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (Sum.inr (result, marks)) (by szg) (by szg)
  have a13 := COMPOSE _ _ (result, marks) a11 a12 (by szg) (by szg) (by szg)
  have := COMPOSE _ _ ((t, h), (result, ((s, marks), idx))) a10 a13 (by szg) (by szg) (by szg)
  sz

/-- The index code of a ready context seen through an outer pair. -/
theorem readyIdx_cost {A : Type} (a : C.Str A) (x : A) (hx : Q.size a x ≤ WF) (s : R.machine.State)
    (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F)) (hml : marks.length ≤ cap)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width)
    (hctx : Q.size (prod a (readyCtx rep R)) (x, ((s, marks), idx)) ≤ WF) :
    Q.cost (Q.compose (QP.snd a (readyCtx rep R)) (readyIdxCode rep R)) (x, ((s, marks), idx)) ≤ 3 * tick := by
  have hh := S.fcaps.hdr
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hready := pair_size S.sizes R.state mRep s marks hs hm
  have hctx1 := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  nz
  unfold readyIdxCode
  have a1 := SND a (readyRep rep R |> fun r => prod r bdI.idx) (x, ((s, marks), idx)) (by szg) (by szg)
  have a2 := SND (readyRep rep R) bdI.idx ((s, marks), idx) (by szg) (by szg)
  have := COMPOSE _ _ (x, ((s, marks), idx)) a1 a2 (by szg) (by szg) (by szg)
  sz

/-- The attacker returned: the wrapper waits for the hash of the forgery's period. -/
theorem finishReadyCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hr : Q.size bdI.out result ≤ headWidth)
    (h : G₁) (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx_def : idx = ⟨.inl (.inr (finalIndex result)), h⟩)
    (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.cost (finishReadyCode rep data cost primitive ports wports R) (result, ((s, marks), idx)) ≤
      2 * adapterTime + comparisonTime + 49 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  obtain ⟨hdec, hout⟩ := S.wcaps.output result (hr.trans S.headRoute)
  have hkey := outputKey_size S result hdec
  have hready := pair_size S.sizes R.state mRep s marks hs hm
  have hctx1 := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  have hctx := pair_size S.sizes bdI.out (readyCtx rep R) result ((s, marks), idx) hr le_rfl
  have hdone := pair_size S.sizes bdI.out mRep result marks hr hm
  have hin := inr_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (result, marks) le_rfl
  have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inr (result, marks)) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (done R.machine result marks) le_rfl
  have tidx := readyIdx_cost S bdI.out result (by sz) s hs marks hml idx hidx (by sz)
  obtain ⟨tdec, hreply⟩ := decodedCode_cost S (prod bdI.out (readyCtx rep R))
    (Q.compose (QP.snd bdI.out (readyCtx rep R)) (readyIdxCode rep R)) (result, ((s, marks), idx)) (by sz) tidx hidx
  have hrepl := pair_size S.sizes (replyRep rep ports) (prod bdI.out (readyCtx rep R)) _ (result, ((s, marks), idx)) hreply le_rfl
  have texp := finishExpectedCode_cost S s hs marks hml result hr idx hidx
  have tnext := finishNextCode_cost S s hs marks hml result hr idx hidx (finalIndex result) (by omega) h
  subst hidx_def
  nz
  have texpect := expectHashCode_cost S (finishExpectedCode rep ports wports R) (finishNextCode rep R)
    (result, ((s, marks), ⟨.inl (.inr (finalIndex result)), h⟩)) (by szg) h (by exact hreply) texp
    (by exact hkey.trans (by omega)) tnext (by szg)
  unfold finishReadyCode
  apply CAST
  have := COMPOSE _ _ (result, ((s, marks), _)) tdec texpect (by szg) (by szg) (by szg)
  sz

theorem holdExpectedCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.cost (holdExpectedCode rep R) (m, ((s, marks), idx)) ≤ 3 * tick := by
  have hh := S.fcaps.hdr
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hkey : Q.size kRep m.1 ≤ Q.size msgRep m := S.sizes.fst_le _ _ m
  have hready := pair_size S.sizes R.state mRep s marks hs hm
  have hctx1 := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  have hctx := pair_size S.sizes msgRep (readyCtx rep R) m ((s, marks), idx) hmsg le_rfl
  nz
  unfold holdExpectedCode
  apply CAST
  have a1 := FST msgRep (readyCtx rep R) (m, ((s, marks), idx)) (by szg) (by szg)
  have a2 := FST kRep (rep.ty scalar) m (by szg) (by szg)
  have := COMPOSE _ _ (m, ((s, marks), idx)) a1 a2 (by szg) (by szg) (by szg)
  sz

theorem holdNextCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width) (t : K)
    (ht : Q.size kRep t ≤ 8 * width) (h : G₁) :
    Q.cost (holdNextCode rep R) ((t, h), (m, ((s, marks), idx))) ≤ 23 * tick := by
  have hh := S.fcaps.hdr
  have hpt := S.point₁ h
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hready := pair_size S.sizes R.state mRep s marks hs hm
  have hctx1 := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  have hctx := pair_size S.sizes msgRep (readyCtx rep R) m ((s, marks), idx) hmsg le_rfl
  have hth := pair_size S.sizes kRep pRep t h ht hpt
  have hpair := pair_size S.sizes (prod kRep pRep) (prod msgRep (readyCtx rep R)) (t, h) (m, ((s, marks), idx)) le_rfl le_rfl
  have hhm := pair_size S.sizes pRep mRep h marks hpt hm
  have hgot := pair_size S.sizes R.state (prod pRep mRep) s (h, marks) hs hhm
  have hin := inl_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (s, h, marks) le_rfl
  have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inl (s, h, marks)) le_rfl
  nz
  unfold holdNextCode
  apply CAST
  have a1 := SND (prod kRep pRep) (prod msgRep (readyCtx rep R)) ((t, h), (m, ((s, marks), idx))) (by szg) (by szg)
  have a2 := SND msgRep (readyCtx rep R) (m, ((s, marks), idx)) (by szg) (by szg)
  have a3 := FST (readyRep rep R) bdI.idx ((s, marks), idx) (by szg) (by szg)
  have a4 := FST R.state mRep (s, marks) (by szg) (by szg)
  have a5 := COMPOSE _ _ ((s, marks), idx) a3 a4 (by szg) (by szg) (by szg)
  have a6 := COMPOSE _ _ (m, ((s, marks), idx)) a2 a5 (by szg) (by szg) (by szg)
  have a7 := COMPOSE _ _ ((t, h), (m, ((s, marks), idx))) a1 a6 (by szg) (by szg) (by szg)
  have b1 := FST (prod kRep pRep) (prod msgRep (readyCtx rep R)) ((t, h), (m, ((s, marks), idx))) (by szg) (by szg)
  have b2 := SND kRep pRep (t, h) (by szg) (by szg)
  have b3 := COMPOSE _ _ ((t, h), (m, ((s, marks), idx))) b1 b2 (by szg) (by szg) (by szg)
  have b4 := SND R.state mRep (s, marks) (by szg) (by szg)
  have b5 := COMPOSE _ _ ((s, marks), idx) a3 b4 (by szg) (by szg) (by szg)
  have b6 := COMPOSE _ _ (m, ((s, marks), idx)) a2 b5 (by szg) (by szg) (by szg)
  have b7 := COMPOSE _ _ ((t, h), (m, ((s, marks), idx))) a1 b6 (by szg) (by szg) (by szg)
  have b8 := PAIR _ _ ((t, h), (m, ((s, marks), idx))) b3 b7 (by szg) (by szg)
  have c1 := PAIR _ _ ((t, h), (m, ((s, marks), idx))) a7 b8 (by szg) (by szg)
  have c2 := INL (gotRep rep R) (doneRep rep (bdI := bdI)) (s, h, marks) (by szg) (by szg)
  have c3 := INR (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (Sum.inl (s, h, marks)) (by szg) (by szg)
  have c4 := COMPOSE _ _ (s, h, marks) c2 c3 (by szg) (by szg) (by szg)
  have := COMPOSE _ _ ((t, h), (m, ((s, marks), idx))) c1 c4 (by szg) (by szg) (by szg)
  sz

/-- The attacker asked to sign: the wrapper waits for the period's hash and holds it. -/
theorem holdHashCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width) (h : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx_def : idx = ⟨.inl (.inr m.1), h⟩)
    (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.cost (holdHashCode rep data cost primitive ports wports R) (m, ((s, marks), idx)) ≤
      adapterTime + comparisonTime + 54 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hkey : Q.size kRep m.1 ≤ Q.size msgRep m := S.sizes.fst_le _ _ m
  have hready := pair_size S.sizes R.state mRep s marks hs hm
  have hctx1 := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  have hctx := pair_size S.sizes msgRep (readyCtx rep R) m ((s, marks), idx) hmsg le_rfl
  have hhm := pair_size S.sizes pRep mRep h marks (S.point₁ h) hm
  have hgot := pair_size S.sizes R.state (prod pRep mRep) s (h, marks) hs hhm
  have hin := inl_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (s, h, marks) le_rfl
  have hin' := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (.inl (s, h, marks)) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (gotHash R.machine s h marks) le_rfl
  have tidx := readyIdx_cost S msgRep m (by sz) s hs marks hml idx hidx (by sz)
  obtain ⟨tdec, hreply⟩ := decodedCode_cost S (prod msgRep (readyCtx rep R))
    (Q.compose (QP.snd msgRep (readyCtx rep R)) (readyIdxCode rep R)) (m, ((s, marks), idx)) (by sz) tidx hidx
  have hrepl := pair_size S.sizes (replyRep rep ports) (prod msgRep (readyCtx rep R)) _ (m, ((s, marks), idx)) hreply le_rfl
  have texp := holdExpectedCode_cost S s hs marks hml m hmsg idx hidx
  have tnext := holdNextCode_cost S s hs marks hml m hmsg idx hidx m.1 (by omega) h
  subst hidx_def
  nz
  have texpect := expectHashCode_cost S (holdExpectedCode rep R) (holdNextCode rep R) (m, ((s, marks), ⟨.inl (.inr m.1), h⟩))
    (by szg) h (by exact hreply) texp (by szg) tnext (by szg)
  unfold holdHashCode
  apply CAST
  have := COMPOSE _ _ (m, ((s, marks), _)) tdec texpect (by szg) (by szg) (by szg)
  sz

end Signatures.Runtime.SyncWrapGeneral
