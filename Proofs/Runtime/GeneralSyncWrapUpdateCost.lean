import Proofs.Runtime.GeneralSyncWrapHeadCost

/-! # Cost of the wrapper's transition, part one: the pieces

Marks, the continuation of the attacker, the decoded reply and the hash-expectation check. Each
is bounded at an enabled input: the decoded tagged reply carries the hashed period the wrapper
is waiting for, so the comparison succeeds and the continuation is taken. -/

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

/-- Normalize every representation abbreviation, then close a size or cost inequality. -/
local macro "sz" : tactic => `(tactic| (
  (try dsimp only [readyRep, gotRep, doneRep, stateRep, marksRep, posRep, replyRep, readyCtx, gotCtx, signCtx, signFrame,
    outerBoundary, Weights.syncMessage, OutTy, AGM.outputTy, markTy, LanguageRepresentation.ty, LanguageRepresentation.env,
    PFunctor.DynSystem.DynComputation.Boundary.head, PFunctor.DynSystem.DynComputation.Boundary.stateIdx,
    WeightedAGM.generalPositions, finalIndex, wrapFrame, ready, gotHash, done, markHash, markSign, Sum.elim_inl, Sum.elim_inr,
    Option.bind, Option.map, Function.comp_def, id] at *);
  (try simp only [arithmetic, eq_self_iff_true, decide_true, ite_true, Sum.elim_inl, Sum.elim_inr] at *);
  omega))


/-! ## Marks -/

theorem markHashCode_cost : Q.cost (markHashCode rep data cost primitive) () ≤ opTime + 2 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hb0 := S.fcaps.bool false
  have hb1 := S.fcaps.bool true
  have hz := S.fcaps.scalar 0
  have hzero := ((primitiveBound CryptoOp.zero).cost_le ()).trans S.fcaps.zero
  have hmark : Q.size (rep.ty markTy) (false, (arithmetic F G₁ G₂ K M cost).execute CryptoOp.zero ()) ≤ 3 * width :=
    mark_size rep S.sizes S.lists width hh S.fcaps.bool S.fcaps.scalar markHash
  unfold markHashCode
  apply CAST
  have t1 := BOOLC false (by sz) (by sz)
  have := PAIR _ _ () t1 hzero (by sz) (by sz)
  sz

theorem markSignCode_cost (m : K × F) (hm : Q.size msgRep m ≤ width) :
    Q.cost (markSignCode rep data correction finalFn keys code) m ≤ routineTime + 4 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hb0 := S.fcaps.bool false
  have hb1 := S.fcaps.bool true
  have hz := S.fcaps.scalar 0
  have hcorr := S.scaps.corr m (by omega)
  have hmark := mark_size rep S.sizes S.lists width hh S.fcaps.bool S.fcaps.scalar (markSign correction m)
  unfold markSignCode
  apply CAST
  have t1 := UNITC msgRep m (by sz) (by sz)
  have t2 := BOOLC true (by sz) (by sz)
  have t3 := COMPOSE _ _ m t1 t2 (by sz) (by sz) (by sz)
  have := PAIR _ _ m t3 hcorr (by sz) (by sz)
  sz

/-- Marks of bounded length, before and after one more mark. -/
theorem marks_sizes (marks : List (Mark F)) (hml : marks.length ≤ cap) (m : Mark F) :
    Q.size mRep marks ≤ marksWidth width (cap + 1) ∧ Q.size mRep (m :: marks) ≤ marksWidth width (cap + 1) ∧
      Q.size (rep.ty markTy) m ≤ 3 * width := by
  have hh := S.fcaps.hdr
  refine ⟨(marks_size rep S.sizes S.lists width cap hh S.fcaps.bool S.fcaps.scalar marks hml).trans
    (marksWidth_le_succ width cap), ?_, mark_size rep S.sizes S.lists width hh S.fcaps.bool S.fcaps.scalar m⟩
  exact marks_size rep S.sizes S.lists width (cap + 1) hh S.fcaps.bool S.fcaps.scalar (m :: marks) (by simp; omega)

theorem recordHashCode_cost (marks : List (Mark F)) (hml : marks.length ≤ cap) :
    Q.cost (recordHashCode rep data cost primitive) marks ≤ opTime + 8 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hb0 := S.fcaps.bool false
  have hb1 := S.fcaps.bool true
  have hz := S.fcaps.scalar 0
  obtain ⟨hm, hm', hmark⟩ := marks_sizes S marks hml markHash
  have tmark := markHashCode_cost S
  have hpair := pair_size S.sizes (rep.ty markTy) mRep markHash marks hmark hm
  unfold recordHashCode
  apply CAST
  have t1 := UNITC mRep marks (by sz) (by sz)
  have t2 := COMPOSE _ _ marks t1 tmark (by sz) (by sz) (by sz)
  have t3 := IDENT mRep marks (by sz)
  have t4 := PAIR _ _ marks t2 t3 (by sz) (by sz)
  have t5 := CONSC (rep.ty markTy) (markHash, marks) (by sz) (by sz)
  have := COMPOSE _ _ marks t4 t5 (by sz) (by sz) (by sz)
  sz

theorem keepMarksCode_cost (marks : List (Mark F)) (hml : marks.length ≤ cap) :
    Q.cost (keepMarksCode rep) marks ≤ tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hb0 := S.fcaps.bool false
  have hb1 := S.fcaps.bool true
  have hz := S.fcaps.scalar 0
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  unfold keepMarksCode
  exact IDENT mRep marks (by sz)

/-! ## Continuing the attacker -/

theorem readyAgainCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F))
    (hm : Q.size mRep marks ≤ marksWidth width (cap + 1)) :
    Q.cost (readyAgainCode rep R) (s, marks) ≤ 3 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hb0 := S.fcaps.bool false
  have hb1 := S.fcaps.bool true
  have hz := S.fcaps.scalar 0
  have hp := pair_size S.sizes R.state mRep s marks hs hm
  have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s, marks) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (ready R.machine s marks) le_rfl
  unfold readyAgainCode
  apply CAST
  have t1 := INL (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s, marks) (by sz) (by sz)
  have t2 := SOME (stateRep rep R) (ready R.machine s marks) (by sz) (by sz)
  have := COMPOSE _ _ (s, marks) t1 t2 (by sz) (by sz) (by sz)
  sz

/-- An enabled tagged reply of the attacker: the position it exposes, with any direction. -/
theorem fedCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width)
    (hupd : Q.cost R.updateCode (s, idx) ≤ work) (s' : R.machine.State) (hnext : R.machine.update? (s, idx) = some s')
    (hs' : Q.size R.state s' ≤ stateWidth) :
    Q.cost (fedCode rep R) ((s, marks), idx) ≤ work + 6 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hb0 := S.fcaps.bool false
  have hb1 := S.fcaps.bool true
  have hz := S.fcaps.scalar 0
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hp := pair_size S.sizes R.state mRep s marks hs hm
  have hctx := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  have hsi := pair_size S.sizes R.state bdI.idx s idx hs hidx
  have hres : Q.size (opt R.state) (R.machine.update? (s, idx)) ≤ stateWidth + header := by
    rw [hnext]; exact some_size S.sizes R.state s' hs'
  unfold fedCode
  apply CAST
  have t1 := FST (readyRep rep R) bdI.idx ((s, marks), idx) (by sz) (by sz)
  have t2 := FST R.state mRep (s, marks) (by sz) (by sz)
  have t3 := COMPOSE _ _ ((s, marks), idx) t1 t2 (by sz) (by sz) (by sz)
  have t4 := SND (readyRep rep R) bdI.idx ((s, marks), idx) (by sz) (by sz)
  have t5 := PAIR _ _ ((s, marks), idx) t3 t4 (by sz) (by sz)
  have := COMPOSE _ _ ((s, marks), idx) t5 hupd (by sz) (by sz) (by sz)
  sz

/-- Feeding an enabled reply and recording with a mark code of known cost. -/
theorem stepReadyCode_cost {update : List (Mark F) → List (Mark F)} (markCode : Q.Realizer mRep mRep update)
    (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (marks : List (Mark F)) (hml : marks.length ≤ cap)
    (hml' : (update marks).length ≤ cap + 1) {Tm : Nat} (tmark : Q.cost markCode marks ≤ Tm)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width)
    (hupd : Q.cost R.updateCode (s, idx) ≤ work) (s' : R.machine.State) (hnext : R.machine.update? (s, idx) = some s')
    (hs' : Q.size R.state s' ≤ stateWidth) :
    Q.cost (stepReadyCode rep R markCode) ((s, marks), idx) ≤ work + Tm + 16 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hb0 := S.fcaps.bool false
  have hb1 := S.fcaps.bool true
  have hz := S.fcaps.scalar 0
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hm' : Q.size mRep (update marks) ≤ marksWidth width (cap + 1) :=
    marks_size rep S.sizes S.lists width (cap + 1) hh S.fcaps.bool S.fcaps.scalar _ hml'
  have hp := pair_size S.sizes R.state mRep s marks hs hm
  have hctx := pair_size S.sizes (readyRep rep R) bdI.idx (s, marks) idx le_rfl hidx
  have hres : Q.size (opt R.state) (R.machine.update? (s, idx)) ≤ stateWidth + header := by
    rw [hnext]; exact some_size S.sizes R.state s' hs'
  have hp' := pair_size S.sizes R.state mRep s' (update marks) hs' hm'
  have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s', update marks) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (ready R.machine s' (update marks)) le_rfl
  have hfed := fedCode_cost S s hs marks hml idx hidx hupd s' hnext hs'
  have hframe := pair_size S.sizes (opt R.state) mRep (R.machine.update? (s, idx)) (update marks) hres hm'
  have tagain : ∀ v, R.machine.update? (s, idx) = some v → Q.cost (readyAgainCode rep R) (v, update marks) ≤ 3 * tick := by
    intro v hv
    rw [hnext] at hv
    cases hv
    exact readyAgainCode_cost S s' hs' (update marks) hm'
  unfold stepReadyCode
  apply CAST
  have t1 := FST (readyRep rep R) bdI.idx ((s, marks), idx) (by sz) (by sz)
  have t2 := SND R.state mRep (s, marks) (by sz) (by sz)
  have t3 := COMPOSE _ _ (s, marks) t2 tmark (by sz) (by sz) (by sz)
  have t4 := COMPOSE _ _ ((s, marks), idx) t1 t3 (by sz) (by sz) (by sz)
  have t5 := PAIR _ _ ((s, marks), idx) hfed t4 (by sz) (by sz)
  have t6 := BIND (readyAgainCode rep R) (R.machine.update? (s, idx), update marks) tagain (by sz)
    (by rw [hnext]; sz)
  have := COMPOSE _ _ ((s, marks), idx) t5 t6 (by sz) (by sz) (by rw [hnext]; sz)
  sz

/-! ## Decoding a reply and expecting a hash -/

/-- Decoding the tagged reply of a context whose index code is bounded. -/
theorem decodedCode_cost {E : Type} (e : C.Str E)
    {idxOf : E → GeneralIndex (key.Value (cryptoBase F G₁ G₂ K M)) (Weights.syncMessage.Value (cryptoBase F G₁ G₂ K M)) G₁ randomBound}
    (idxCode : Q.Realizer e bdI.idx idxOf) (ctx : E) (hctx : Q.size e ctx + 16 * width ≤ WF) {Ti : Nat}
    (tidx : Q.cost idxCode ctx ≤ Ti) (hidx : Q.size bdI.idx (idxOf ctx) ≤ 8 * width) :
    Q.cost (decodedCode rep ports wports e idxCode) ctx ≤ Ti + adapterTime + 3 * tick ∧
      Q.size (replyRep rep ports) (decodeIdx F G₁ G₂ K M randomBound (idxOf ctx)) ≤ 8 * width := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hb0 := S.fcaps.bool false
  have hb1 := S.fcaps.bool true
  have hz := S.fcaps.scalar 0
  obtain ⟨hdec, treply⟩ := S.wcaps.reply _ hidx
  have hp := pair_size S.sizes (replyRep rep ports) e _ ctx hdec le_rfl
  refine ⟨?_, hdec⟩
  unfold decodedCode
  apply CAST
  have t1 := COMPOSE _ _ ctx tidx treply (by sz) (by sz) (by sz)
  have t2 := IDENT e ctx (by sz)
  have := PAIR _ _ ctx t1 t2 (by sz) (by sz)
  sz

/-- The comparison of the hashed period with the expected one, at an enabled decoded reply: the
periods agree, so the continuation runs. -/
theorem compare_cost {E : Type} {e : C.Str E} {expected : E → K} (expectedCode : Q.Realizer e kRep expected)
    {next : (K × G₁) × E → State R.machine (F := F)}
    (nextCode : Q.Realizer (prod (prod kRep pRep) e) (stateRep rep R) next)
    (ctx : E) (hctx : Q.size e ctx + 16 * width ≤ WF) (h : G₁)
    (hreply : Q.size (replyRep rep ports) (.inr (.inl (expected ctx, h))) ≤ 8 * width)
    {Te Tn : Nat} (texp : Q.cost expectedCode ctx ≤ Te) (hexp : Q.size kRep (expected ctx) ≤ 8 * width)
    (tnext : Q.cost nextCode ((expected ctx, h), ctx) ≤ Tn)
    (hnext : Q.size (stateRep rep R) (next ((expected ctx, h), ctx)) + 16 * width ≤ WF) :
    Q.cost (Q.compose
      (QP.pair (Q.compose (QP.pair (Q.compose (QP.fst (prod kRep pRep) e) (QP.fst kRep pRep))
          (Q.compose (QP.snd (prod kRep pRep) e) expectedCode)) (primitive CryptoOp.keyEq))
        (Q.identity (prod (prod kRep pRep) e)))
      (Q.compose (data.select (prod (prod kRep pRep) e))
        (QS.elim (Q.compose nextCode (OC.someCode (stateRep rep R)))
          (QO.none (prod (prod kRep pRep) e) (stateRep rep R))))) ((expected ctx, h), ctx) ≤
      Te + Tn + comparisonTime + 15 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hu := S.fcaps.unit
  have hbt := S.fcaps.bool true
  have hpt := S.point₁ h
  have hth := inr_payload S.sizes _ _ _ hreply
  have hth' := inl_payload S.sizes _ _ _ hth
  have hpair := pair_size S.sizes (prod kRep pRep) e (expected ctx, h) ctx hth' le_rfl
  have hkk := pair_size S.sizes kRep kRep (expected ctx) (expected ctx) hexp hexp
  have hbool := pair_size S.sizes rep.data.bool (prod (prod kRep pRep) e) true ((expected ctx, h), ctx) hbt hpair
  have hsel := inl_size S.sizes (prod (prod kRep pRep) e) (prod (prod kRep pRep) e) ((expected ctx, h), ctx) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (next ((expected ctx, h), ctx)) le_rfl
  have hkeyEq := ((primitiveBound CryptoOp.keyEq).cost_le (expected ctx, expected ctx)).trans (S.keyEq _ _ hexp hexp)
  have c1 := FST (prod kRep pRep) e ((expected ctx, h), ctx) (by sz) (by sz)
  have c2 := FST kRep pRep (expected ctx, h) (by sz) (by sz)
  have c3 := COMPOSE _ _ ((expected ctx, h), ctx) c1 c2 (by sz) (by sz) (by sz)
  have c4 := SND (prod kRep pRep) e ((expected ctx, h), ctx) (by sz) (by sz)
  have c5 := COMPOSE _ _ ((expected ctx, h), ctx) c4 texp (by sz) (by sz) (by sz)
  have c6 := PAIR _ _ ((expected ctx, h), ctx) c3 c5 (by sz) (by sz)
  have c7 := COMPOSE _ _ ((expected ctx, h), ctx) c6 hkeyEq (by sz) (by sz) (by sz)
  have c8 := IDENT (prod (prod kRep pRep) e) ((expected ctx, h), ctx) (by sz)
  have c9 := PAIR _ _ ((expected ctx, h), ctx) c7 c8 (by sz) (by sz)
  have c10 := SELECT (prod (prod kRep pRep) e) (true, ((expected ctx, h), ctx)) (by sz) (by sz)
  have c11 := SOME (stateRep rep R) (next ((expected ctx, h), ctx)) (by sz) (by sz)
  have c12 := COMPOSE _ _ ((expected ctx, h), ctx) tnext c11 (by sz) (by sz) (by sz)
  have c13 := ELIML _ (QO.none (prod (prod kRep pRep) e) (stateRep rep R)) ((expected ctx, h), ctx) c12 (by sz) (by sz)
  have c14 := COMPOSE _ _ (true, ((expected ctx, h), ctx)) c10 c13 (by sz) (by sz) (by sz)
  have := COMPOSE _ _ ((expected ctx, h), ctx) c9 (by sz) (by sz) (by sz) (by sz)
  sz

/-- The hash expectation at an enabled decoded reply. -/
theorem expectHashCode_cost {E : Type} {e : C.Str E} {expected : E → K} (expectedCode : Q.Realizer e kRep expected)
    {next : (K × G₁) × E → State R.machine (F := F)}
    (nextCode : Q.Realizer (prod (prod kRep pRep) e) (stateRep rep R) next)
    (ctx : E) (hctx : Q.size e ctx + 16 * width ≤ WF) (h : G₁)
    (hreply : Q.size (replyRep rep ports) (.inr (.inl (expected ctx, h))) ≤ 8 * width)
    {Te Tn : Nat} (texp : Q.cost expectedCode ctx ≤ Te) (hexp : Q.size kRep (expected ctx) ≤ 8 * width)
    (tnext : Q.cost nextCode ((expected ctx, h), ctx) ≤ Tn)
    (hnext : Q.size (stateRep rep R) (next ((expected ctx, h), ctx)) + 16 * width ≤ WF) :
    Q.cost (expectHashCode rep data cost primitive ports R expectedCode nextCode) (.inr (.inl (expected ctx, h)), ctx) ≤
      Te + Tn + comparisonTime + 21 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hpt := S.point₁ h
  have hth := inr_payload S.sizes _ _ _ hreply
  have hth' := inl_payload S.sizes _ _ _ hth
  have hpair := pair_size S.sizes (prod kRep pRep) e (expected ctx, h) ctx hth' le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (next ((expected ctx, h), ctx)) le_rfl
  have hin := inl_size S.sizes (prod (prod kRep pRep) e) (prod (prod msgRep pRep) e) ((expected ctx, h), ctx) le_rfl
  have hrepl := pair_size S.sizes (replyRep rep ports) e _ ctx hreply le_rfl
  have hin2 := inl_size S.sizes (prod kRep pRep) (prod msgRep pRep) (expected ctx, h) le_rfl
  have hrp := pair_size S.sizes (sum (prod kRep pRep) (prod msgRep pRep)) e (Sum.inl (expected ctx, h)) ctx le_rfl le_rfl
  have hd1 := inr_size S.sizes (prod ports.randomReply e) (prod (sum (prod kRep pRep) (prod msgRep pRep)) e)
    (Sum.inl (expected ctx, h), ctx) le_rfl
  have compare := compare_cost S expectedCode nextCode ctx hctx h hreply texp hexp tnext hnext
  unfold expectHashCode
  dsimp only
  apply CAST
  unfold QuantitativeStepClass.IsDistributive.elimContext
  apply CAST
  have d1 := DISTRIBUTE ports.randomReply (sum (prod kRep pRep) (prod msgRep pRep)) e (Sum.inr (Sum.inl (expected ctx, h)), ctx)
    (by sz) (by sz)
  have d2 := DISTRIBUTE (prod kRep pRep) (prod msgRep pRep) e (Sum.inl (expected ctx, h), ctx) (by sz) (by sz)
  have d3 := ELIML _ (QO.none (prod (prod msgRep pRep) e) (stateRep rep R)) ((expected ctx, h), ctx) compare (by sz) (by sz)
  have d4 := COMPOSE _ _ (Sum.inl (expected ctx, h), ctx) d2 d3 (by sz) (by sz) (by sz)
  exact le_trans (COMPOSE _ _ (Sum.inr (Sum.inl (expected ctx, h)), ctx) d1
    (ELIMR _ _ (Sum.inl (expected ctx, h), ctx) (CAST _ _ _ d4) (by sz) (by sz)) (by sz) (by sz) (by sz)) (by sz)

end Signatures.Runtime.SyncWrapGeneral
