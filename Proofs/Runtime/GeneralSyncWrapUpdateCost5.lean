import Proofs.Runtime.GeneralSyncWrapUpdateCost4

/-! # Cost of the wrapper's transition, part five: the signature reply

When the signature of the held period arrives, the wrapper corrects it with the scheme's routine,
feeds it to the attacker at its pending signing position and records the signing mark. -/

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




/-! ## Correcting and feeding a signature -/

/-- Sizes of the signing frame's components. -/
theorem signFrame_sizes (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (h : G₁) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width) (σ : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.size (signFrame rep R) ((m, σ), (m, ((s, h, marks), idx))) + 16 * width ≤ WF ∧
    Q.size (signCtx rep R) (m, ((s, h, marks), idx)) + 16 * width ≤ WF ∧
    Q.size (gotCtx rep R) ((s, h, marks), idx) + 16 * width ≤ WF ∧
    Q.size (gotRep rep R) (s, h, marks) + 16 * width ≤ WF := by
  have hh := S.fcaps.hdr
  have hpt := S.point₁ h
  have hσ := S.point₁ σ
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hhm := pair_size S.sizes pRep mRep h marks hpt hm
  have hgot := pair_size S.sizes R.state (prod pRep mRep) s (h, marks) hs hhm
  have hctx := pair_size S.sizes (gotRep rep R) bdI.idx (s, h, marks) idx le_rfl hidx
  have hsctx := pair_size S.sizes msgRep (gotCtx rep R) m ((s, h, marks), idx) hmsg le_rfl
  have hmσ := pair_size S.sizes msgRep pRep m σ hmsg hσ
  have hframe := pair_size S.sizes (prod msgRep pRep) (signCtx rep R) (m, σ) (m, ((s, h, marks), idx)) le_rfl le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> sz

theorem heldCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (h : G₁) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width) (σ : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.cost (heldCode rep R) ((m, σ), (m, ((s, h, marks), idx))) ≤ 9 * tick := by
  have hh := S.fcaps.hdr
  have hpt := S.point₁ h
  obtain ⟨hm, -, -⟩ := marks_sizes S marks hml markHash
  have hhm := pair_size S.sizes pRep mRep h marks hpt hm
  obtain ⟨hframe, hsctx, hctx, hgot⟩ := signFrame_sizes S s hs h marks hml m hmsg σ idx hidx
  nz
  unfold heldCode
  apply CAST
  have a1 := SND (prod msgRep pRep) (signCtx rep R) ((m, σ), (m, ((s, h, marks), idx))) (by szg) (by szg)
  have a2 := SND msgRep (gotCtx rep R) (m, ((s, h, marks), idx)) (by szg) (by szg)
  have a3 := FST (gotRep rep R) bdI.idx ((s, h, marks), idx) (by szg) (by szg)
  have a4 := SND R.state (prod pRep mRep) (s, h, marks) (by szg) (by szg)
  have a5 := FST pRep mRep (h, marks) (by szg) (by szg)
  have a6 := COMPOSE _ _ (s, h, marks) a4 a5 (by szg) (by szg) (by szg)
  have a7 := COMPOSE _ _ ((s, h, marks), idx) a3 a6 (by szg) (by szg) (by szg)
  have a8 := COMPOSE _ _ (m, ((s, h, marks), idx)) a2 a7 (by szg) (by szg) (by szg)
  have := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) a1 a8 (by szg) (by szg) (by szg)
  sz

theorem correctedCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (h : G₁) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width) (σ : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.cost (correctedCode rep cost primitive correction finalFn keys code R) ((m, σ), (m, ((s, h, marks), idx))) ≤
      routineTime + 2 * opTime + 21 * tick := by
  have hh := S.fcaps.hdr
  have hpt := S.point₁ h
  have hσ := S.point₁ σ
  have hc := S.fcaps.scalar (correction m)
  have hch := S.point₁ (correction m • h)
  have hσ' := S.point₁ (σ + correction m • h)
  have hcorr := S.scaps.corr m (by omega)
  have hscale := ((primitiveBound CryptoOp.scale₁).cost_le (correction m, h)).trans (S.scale₁ _ _)
  have hadd := ((primitiveBound CryptoOp.add₁).cost_le (σ, correction m • h)).trans (S.add₁ _ _)
  have hmσ := pair_size S.sizes msgRep pRep m σ hmsg hσ
  have hcp := pair_size S.sizes (rep.ty scalar) pRep (correction m) h hc hpt
  have hσp := pair_size S.sizes pRep pRep σ (correction m • h) hσ hch
  obtain ⟨hframe, hsctx, hctx, hgot⟩ := signFrame_sizes S s hs h marks hml m hmsg σ idx hidx
  have theld := heldCode_cost S s hs h marks hml m hmsg σ idx hidx
  nz
  unfold correctedCode
  apply CAST
  have a1 := FST (prod msgRep pRep) (signCtx rep R) ((m, σ), (m, ((s, h, marks), idx))) (by szg) (by szg)
  have a2 := SND msgRep pRep (m, σ) (by szg) (by szg)
  have a3 := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) a1 a2 (by szg) (by szg) (by szg)
  have b1 := FST msgRep pRep (m, σ) (by szg) (by szg)
  have b2 := COMPOSE _ _ (m, σ) b1 hcorr (by szg) (by szg) (by szg)
  have b3 := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) a1 b2 (by szg) (by szg) (by szg)
  have b4 := PAIR _ _ ((m, σ), (m, ((s, h, marks), idx))) b3 theld (by szg) (by szg)
  have b5 := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) b4 hscale (by szg) (by szg) (by szg)
  have c1 := PAIR _ _ ((m, σ), (m, ((s, h, marks), idx))) a3 b5 (by szg) (by szg)
  have := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) c1 hadd (by szg) (by szg) (by szg)
  sz

theorem markedCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (h : G₁) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width) (σ : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width) :
    Q.cost (markedCode rep data correction finalFn keys code R) ((m, σ), (m, ((s, h, marks), idx))) ≤
      routineTime + 20 * tick := by
  have hh := S.fcaps.hdr
  have hpt := S.point₁ h
  have hσ := S.point₁ σ
  obtain ⟨hm, hm', hmark⟩ := marks_sizes S marks hml (markSign correction m)
  have hhm := pair_size S.sizes pRep mRep h marks hpt hm
  have hpair := pair_size S.sizes (rep.ty markTy) mRep (markSign correction m) marks hmark hm
  have hmσ := pair_size S.sizes msgRep pRep m σ hmsg hσ
  obtain ⟨hframe, hsctx, hctx, hgot⟩ := signFrame_sizes S s hs h marks hml m hmsg σ idx hidx
  have tmark := markSignCode_cost S m hmsg
  nz
  unfold markedCode
  apply CAST
  have a1 := FST (prod msgRep pRep) (signCtx rep R) ((m, σ), (m, ((s, h, marks), idx))) (by szg) (by szg)
  have a2 := FST msgRep pRep (m, σ) (by szg) (by szg)
  have a3 := COMPOSE _ _ (m, σ) a2 tmark (by szg) (by szg) (by szg)
  have a4 := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) a1 a3 (by szg) (by szg) (by szg)
  have b1 := SND (prod msgRep pRep) (signCtx rep R) ((m, σ), (m, ((s, h, marks), idx))) (by szg) (by szg)
  have b2 := SND msgRep (gotCtx rep R) (m, ((s, h, marks), idx)) (by szg) (by szg)
  have b3 := FST (gotRep rep R) bdI.idx ((s, h, marks), idx) (by szg) (by szg)
  have b4 := SND R.state (prod pRep mRep) (s, h, marks) (by szg) (by szg)
  have b5 := SND pRep mRep (h, marks) (by szg) (by szg)
  have b6 := COMPOSE _ _ (s, h, marks) b4 b5 (by szg) (by szg) (by szg)
  have b7 := COMPOSE _ _ ((s, h, marks), idx) b3 b6 (by szg) (by szg) (by szg)
  have b8 := COMPOSE _ _ (m, ((s, h, marks), idx)) b2 b7 (by szg) (by szg) (by szg)
  have b9 := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) b1 b8 (by szg) (by szg) (by szg)
  have c1 := PAIR _ _ ((m, σ), (m, ((s, h, marks), idx))) a4 b9 (by szg) (by szg)
  have c2 := CONSC (rep.ty markTy) (markSign correction m, marks) (by szg) (by szg)
  have := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) c1 c2 (by szg) (by szg) (by szg)
  sz

/-- Feeding the corrected signature to the attacker, at its enabled signing position. -/
theorem fedSignCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (h : G₁) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width) (σ : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width)
    (hupd : Q.cost R.updateCode (s, tagSign (m, σ + correction m • h)) ≤ work) (s' : R.machine.State)
    (hnext : R.machine.update? (s, tagSign (m, σ + correction m • h)) = some s') (hs' : Q.size R.state s' ≤ stateWidth) :
    Q.cost (fedSignCode rep cost primitive ports correction finalFn keys code R) ((m, σ), (m, ((s, h, marks), idx))) ≤
      work + routineTime + 2 * opTime + adapterTime + 35 * tick := by
  have hh := S.fcaps.hdr
  have hσ := S.point₁ σ
  have hσ' := S.point₁ (σ + correction m • h)
  obtain ⟨hidx', hsign⟩ := S.pcaps.signTag m (σ + correction m • h) hmsg hσ'
  have hmσ := pair_size S.sizes msgRep pRep m σ hmsg hσ
  have hmσ' := pair_size S.sizes msgRep pRep m (σ + correction m • h) hmsg hσ'
  have hsidx := pair_size S.sizes R.state bdI.idx s (tagSign (m, σ + correction m • h)) hs hidx'
  have hres : Q.size (opt R.state) (R.machine.update? (s, tagSign (m, σ + correction m • h))) ≤ stateWidth + header := by
    rw [hnext]; exact some_size S.sizes R.state s' hs'
  obtain ⟨hframe, hsctx, hctx, hgot⟩ := signFrame_sizes S s hs h marks hml m hmsg σ idx hidx
  have tcorr := correctedCode_cost S s hs h marks hml m hmsg σ idx hidx
  nz
  unfold fedSignCode
  apply CAST
  have a1 := SND (prod msgRep pRep) (signCtx rep R) ((m, σ), (m, ((s, h, marks), idx))) (by szg) (by szg)
  have a2 := SND msgRep (gotCtx rep R) (m, ((s, h, marks), idx)) (by szg) (by szg)
  have a3 := FST (gotRep rep R) bdI.idx ((s, h, marks), idx) (by szg) (by szg)
  have a4 := FST R.state (prod pRep mRep) (s, h, marks) (by szg) (by szg)
  have a5 := COMPOSE _ _ ((s, h, marks), idx) a3 a4 (by szg) (by szg) (by szg)
  have a6 := COMPOSE _ _ (m, ((s, h, marks), idx)) a2 a5 (by szg) (by szg) (by szg)
  have a7 := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) a1 a6 (by szg) (by szg) (by szg)
  have b1 := FST (prod msgRep pRep) (signCtx rep R) ((m, σ), (m, ((s, h, marks), idx))) (by szg) (by szg)
  have b2 := FST msgRep pRep (m, σ) (by szg) (by szg)
  have b3 := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) b1 b2 (by szg) (by szg) (by szg)
  have b4 := PAIR _ _ ((m, σ), (m, ((s, h, marks), idx))) b3 tcorr (by szg) (by szg)
  have b5 := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) b4 hsign (by szg) (by szg) (by szg)
  have c1 := PAIR _ _ ((m, σ), (m, ((s, h, marks), idx))) a7 b5 (by szg) (by szg)
  have := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) c1 hupd (by szg) (by szg) (by szg)
  sz

/-- The signature arrived: the attacker continues with the corrected one and the mark recorded. -/
theorem signedCode_cost (s : R.machine.State) (hs : Q.size R.state s ≤ stateWidth) (h : G₁) (marks : List (Mark F))
    (hml : marks.length ≤ cap) (m : K × F) (hmsg : Q.size msgRep m ≤ width) (σ : G₁)
    (idx : GeneralIndex K (K × F) G₁ randomBound) (hidx : Q.size bdI.idx idx ≤ 8 * width)
    (hupd : Q.cost R.updateCode (s, tagSign (m, σ + correction m • h)) ≤ work) (s' : R.machine.State)
    (hnext : R.machine.update? (s, tagSign (m, σ + correction m • h)) = some s') (hs' : Q.size R.state s' ≤ stateWidth) :
    Q.cost (signedCode rep data cost primitive ports correction finalFn keys code R) ((m, σ), (m, ((s, h, marks), idx))) ≤
      work + 2 * routineTime + 2 * opTime + adapterTime + 61 * tick := by
  have hh := S.fcaps.hdr
  obtain ⟨hm, hm', hmark⟩ := marks_sizes S marks hml (markSign correction m)
  have hres : Q.size (opt R.state) (R.machine.update? (s, tagSign (m, σ + correction m • h))) ≤ stateWidth + header := by
    rw [hnext]; exact some_size S.sizes R.state s' hs'
  have hp' := pair_size S.sizes R.state mRep s' (markSign correction m :: marks) hs' hm'
  have hin := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s', markSign correction m :: marks) le_rfl
  have hsome := some_size S.sizes (stateRep rep R) (ready R.machine s' (markSign correction m :: marks)) le_rfl
  have hbind := pair_size S.sizes (opt R.state) mRep (R.machine.update? (s, tagSign (m, σ + correction m • h)))
    (markSign correction m :: marks) hres hm'
  have hval : Q.size (opt (stateRep rep R))
      ((R.machine.update? (s, tagSign (m, σ + correction m • h))).map fun x => ready R.machine x (markSign correction m :: marks)) ≤
      WF := by
    rw [hnext]; sz
  have hval2 : Q.size (opt (stateRep rep R))
      ((R.machine.update? (s, tagSign (m, σ + correction m • h))).bind fun x =>
        some (ready R.machine x (markSign correction m :: marks))) ≤ WF := by
    rw [hnext]; sz
  obtain ⟨hframe, hsctx, hctx, hgot⟩ := signFrame_sizes S s hs h marks hml m hmsg σ idx hidx
  have tfed := fedSignCode_cost S s hs h marks hml m hmsg σ idx hidx hupd s' hnext hs'
  have tmarked := markedCode_cost S s hs h marks hml m hmsg σ idx hidx
  have tagain : ∀ v, R.machine.update? (s, tagSign (m, σ + correction m • h)) = some v →
      Q.cost (readyAgainCode rep R) (v, markSign correction m :: marks) ≤ 3 * tick := by
    intro v hv
    rw [hnext] at hv
    cases hv
    exact readyAgainCode_cost S s' hs' (markSign correction m :: marks) hm'
  nz
  unfold signedCode
  apply CAST
  have a1 := PAIR _ _ ((m, σ), (m, ((s, h, marks), idx))) tfed tmarked (by szg) (by first | exact hbind.trans (by szg) | szg)
  have a2 := BIND (readyAgainCode rep R) (R.machine.update? (s, tagSign (m, σ + correction m • h)), markSign correction m :: marks)
    tagain (by first | exact hbind.trans (by szg) | szg) (by first | exact hval | exact hval2 | szg)
  have := COMPOSE _ _ ((m, σ), (m, ((s, h, marks), idx))) a1 a2 (by szg) (by first | exact hbind.trans (by szg) | szg)
    (by first | exact hval | exact hval2 | szg)
  sz

end Signatures.Runtime.SyncWrapGeneral
