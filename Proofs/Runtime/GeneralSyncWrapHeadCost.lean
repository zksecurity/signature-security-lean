import Proofs.Runtime.GeneralSyncWrapSizes
import Proofs.Runtime.GeneralSyncWrapRealizer

/-! # Cost of the wrapper's readout

The readout runs the attacker's readout once and relabels it with a few structural steps and
adapter calls; from a finished state it runs the compiled finish. Each piece is bounded by its
leaf costs plus one frame fee per structural node. -/

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

attribute [local implicit_reducible] PFunctor.Idx

/-- Every law and cap the wrapper's cost accounting uses. -/
structure Caps (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M)) (data : DataCode Q rep.data)
    (cost : PrimitiveCosts)
    (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
      Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
    (ports : NativePorts (Q := Q) rep key Weights.syncMessage bdI) (wports : WrapPorts rep ports)
    (correction finalFn : K × F → F) (keys : G₂ → G₂ × G₂) (code : SchemeCode (Q := Q) rep correction finalFn keys)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
    (overhead : Nat → Nat) (header : Nat)
    (width cap stateWidth headWidth routeWidth outputWidth finishedRoute adapterTime routineTime opTime
      comparisonTime : Nat) : Prop where
  laws : LocalCostLaws Q overhead
  dispatch : DispatchCostLaws (Q := Q) overhead
  optLaws : OptionCostLaws (Q := Q) overhead
  dataLaws : DataCostLaws rep.data data overhead
  mono : Monotone overhead
  sizes : SizeLaws Q header
  lists : ListSizeLaws Q rep.data header
  lens : ListLengthLaws Q rep.data
  wcaps : WrapPortCaps rep ports wports width routeWidth outputWidth (finishedWidth width cap outputWidth)
    finishedRoute adapterTime
  pcaps : WeightedAGM.NativeHandler.PortCaps rep key Weights.syncMessage bdI ports width adapterTime
  scaps : SchemeCaps (Q := Q) rep correction finalFn keys code width routineTime
  fcaps : FinishCaps (header := header) rep cost primitive primitiveBound width cap opTime
  point₁ : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width
  point₂ : ∀ g : G₂, Q.size (rep.ty point₂) g ≤ width
  outputKey : outputWidth ≤ width
  headRoute : headWidth ≤ routeWidth
  keyEq : ∀ x y : K, Q.size (rep.ty key) x ≤ 8 * width → Q.size (rep.ty key) y ≤ 8 * width →
    (primitiveBound CryptoOp.keyEq).time (x, y) ≤ comparisonTime
  scale₁ : ∀ (x : F) (g : G₁), (primitiveBound CryptoOp.scale₁).time (x, g) ≤ opTime
  add₁ : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ opTime

variable (S : Caps rep data cost primitive ports wports correction finalFn keys code primitiveBound overhead header
  width cap stateWidth headWidth routeWidth outputWidth finishedRoute adapterTime routineTime opTime comparisonTime)

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
local notation "restRep" => rep.ty (Ty.pair scalar (Ty.pair (Ty.list scalar) (Ty.list scalar)))
local notation "COMPOSE" => FrameCost.compose_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "PAIR" => FrameCost.pair_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "FST" => FrameCost.fst_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "SND" => FrameCost.snd_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "IDENT" => FrameCost.identity_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "ELIML" => FrameCost.elim_inl_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "ELIMR" => FrameCost.elim_inr_le S.laws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "INL" => FrameCost.inl_le S.dispatch S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "INR" => FrameCost.inr_le S.dispatch S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "UNITC" => FrameCost.unit_le S.dataLaws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
local notation "CAST" => FrameCost.castFunction_le

/-- Normalize every representation abbreviation, then close a size or cost inequality. -/
local macro "sz" : tactic => `(tactic| (
  (try dsimp only [readyRep, gotRep, doneRep, stateRep, marksRep, posRep, replyRep, readyCtx, gotCtx, signCtx, signFrame,
    outerBoundary, Weights.syncMessage, OutTy, AGM.outputTy, markTy, LanguageRepresentation.ty, LanguageRepresentation.env,
    PFunctor.DynSystem.DynComputation.Boundary.head, PFunctor.DynSystem.DynComputation.Boundary.stateIdx,
    WeightedAGM.generalPositions, finalIndex, wrapFrame, ready, gotHash, done, Sum.elim_inl, Sum.elim_inr,
    Function.comp_def, id] at *);
  omega))

/-! ## Frame facts -/

theorem hdr_le_width : header ≤ width := S.fcaps.hdr

theorem finishedWidth_le_frame : finishedWidth width cap outputWidth ≤ WF := by
  have hmw : marksWidth width (cap + 1) = 4 * (cap * width) + 5 * width := by unfold marksWidth; ring
  have h26 : (2 * cap + 6) * width = 2 * (cap * width) + 6 * width := by ring
  unfold finishedWidth wrapFrame
  sz

/-- The finished output's decoded size. -/
theorem finished_size (r : OutTy.Value (cryptoBase F G₁ G₂ K M))
    (hr : Q.size (rep.ty OutTy) r ≤ outputWidth) (marks : List (Mark F)) (hm : marks.length ≤ cap) :
    Q.size (rep.ty OutTy) (fin finalFn r marks) ≤ finishedWidth width cap outputWidth := by
  obtain ⟨hr1, hr21, hγ, hξ, hγc, hξc, hmk, hmkr, hE0⟩ :=
    finish_facts rep cost primitive primitiveBound S.sizes S.lists S.mono S.fcaps S.lens r marks (finalFn r.1) hr hm
  obtain ⟨hh, hu, hb, hn, hf, _, _, _, _, _, _⟩ := S.fcaps
  have hcoeffs : Q.size (rep.ty (.list scalar)) (remapMarks r.2.2.1 r.2.2.2 marks.reverse 0 0 ++ [-(finalFn r.1)]) ≤
      (2 * cap + 3) * width :=
    scalars_size rep S.sizes S.lists width (cap + 1) hh hf _
      (by simp only [List.length_append, List.length_singleton, remapMarks_length, List.length_reverse]; omega)
  have pA := pair_size S.sizes (rep.ty (.list scalar)) (rep.ty (.list scalar)) _ r.2.2.2 hcoeffs hξ
  have pB := pair_size S.sizes (rep.ty scalar) (rep.ty (.pair (.list scalar) (.list scalar))) r.2.1 _ hr21 pA
  have pC := pair_size S.sizes (rep.ty Weights.syncMessage) (rep.ty (.pair scalar (.pair (.list scalar) (.list scalar))))
    r.1 _ hr1 pB
  change Q.size (rep.ty OutTy) (fin finalFn r marks) ≤ _ at pC
  have h23 : (2 * cap + 3) * width = 2 * (cap * width) + 3 * width := by ring
  have h26 : (2 * cap + 6) * width = 2 * (cap * width) + 6 * width := by ring
  unfold finishedWidth
  sz

/-- The output's key is a sized request payload. -/
theorem outputKey_size (r : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hr : Q.size (rep.ty OutTy) r ≤ outputWidth) :
    Q.size kRep (finalIndex r) ≤ width := by
  have hOK := S.outputKey
  have h1 : Q.size msgRep r.1 ≤ Q.size (rep.ty OutTy) r := S.sizes.fst_le _ _ r
  have h2 : Q.size kRep r.1.1 ≤ Q.size msgRep r.1 := S.sizes.fst_le _ _ r.1
  sz

/-- The hash position of a sized key and its encoding. -/
theorem hashPos_size (t : K) (ht : Q.size kRep t ≤ width) :
    Q.size (posRep rep) (.inl (.inr t) : GeneralRequest K (K × F) randomBound) ≤ 3 * width ∧
      Q.size bdI.pos (.inl (.inr t) : GeneralRequest K (K × F) randomBound) ≤ 8 * width := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have h1 := inr_size S.sizes boundedRep kRep t ht
  have h2 := inl_size S.sizes (sum boundedRep kRep) msgRep (.inr t) h1
  change Q.size (posRep rep) (.inl (.inr t) : GeneralRequest K (K × F) randomBound) ≤ _ at h2
  exact ⟨by omega, (S.wcaps.position _ (by sz)).1⟩

/-! ## Pieces of the readout -/

theorem periodCode_cost (r : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hr : Q.size (rep.ty OutTy) r ≤ outputWidth) :
    Q.cost (periodCode rep) r ≤ 3 * tick := by
  have hWF := output_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h1 : Q.size msgRep r.1 ≤ Q.size (rep.ty OutTy) r := S.sizes.fst_le _ _ r
  have h2 : Q.size kRep r.1.1 ≤ Q.size msgRep r.1 := S.sizes.fst_le _ _ r.1
  unfold periodCode
  apply CAST
  have t1 := FST msgRep restRep r (by exact hr.trans hWF) (by exact h1.trans (hr.trans hWF))
  have t2 := FST kRep (rep.ty scalar) r.1 (by exact h1.trans (hr.trans hWF)) (by exact h2.trans (h1.trans (hr.trans hWF)))
  have := COMPOSE _ _ r t1 t2 (hr.trans hWF) (h1.trans (hr.trans hWF)) (h2.trans (h1.trans (hr.trans hWF)))
  sz

theorem hashPosCode_cost (t : K) (ht : Q.size kRep t ≤ width) :
    Q.cost (hashPosCode rep ports wports) t ≤ adapterTime + 4 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hw := width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h8 := eight_width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h64 := room_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  obtain ⟨hpos, hbd⟩ := hashPos_size S t ht
  have h1 := inr_size S.sizes boundedRep kRep t ht
  have hadapt := (S.wcaps.position _ hpos).2
  unfold hashPosCode
  apply CAST
  have t1 := INR boundedRep kRep t (by sz) (by sz)
  have t2 := INL (sum boundedRep kRep) msgRep (Sum.inr t) (by sz) (by exact hpos.trans (by sz))
  have t3 := COMPOSE _ _ (Sum.inr t) t2 hadapt (by sz) (by exact hpos.trans (by sz)) (by exact hbd.trans h8)
  have := COMPOSE _ _ t t1 t3 (by sz) (by sz) (by exact hbd.trans h8)
  sz

theorem finalPosCode_cost (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hr : Q.size bdI.out result ≤ headWidth) :
    Q.cost (finalPosCode rep ports wports) result ≤ 2 * adapterTime + 9 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hHF := route_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have hOF := output_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h8 := eight_width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h64 := room_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  obtain ⟨hdec, hout⟩ := S.wcaps.output result (hr.trans S.headRoute)
  have hkey := outputKey_size S result hdec
  obtain ⟨hpos, hbd⟩ := hashPos_size S _ hkey
  have tp := periodCode_cost S result hdec
  have th := hashPosCode_cost S _ hkey
  unfold finalPosCode
  apply CAST
  have t2 := COMPOSE _ _ result tp th (hdec.trans hOF) (by exact hkey.trans (by sz)) (by exact hbd.trans h8)
  have := COMPOSE _ _ result hout t2 (by sz) (hdec.trans hOF) (by exact hbd.trans h8)
  sz

theorem translatePosCode_cost (pos : GeneralRequest K (K × F) randomBound)
    (hpos : WeightedAGM.NativeHandler.RequestSized (Q := Q) rep key Weights.syncMessage width pos) :
    Q.cost (translatePosCode rep ports wports) pos ≤ 2 * adapterTime + 8 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hw := width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h8 := eight_width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h64 := room_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have hdec : Q.size (posRep rep) pos ≤ 3 * width :=
    WeightedAGM.NativeHandler.request_size rep key Weights.syncMessage S.sizes width hh pos hpos
  have htr : Q.size (posRep rep) (translatePos pos) ≤ 3 * width :=
    WeightedAGM.NativeHandler.request_size rep key Weights.syncMessage S.sizes width hh _
      (translatePos_sized rep S.sizes width pos hpos)
  obtain ⟨hbd, hreq⟩ := S.pcaps.request pos hpos
  obtain ⟨hbd', hposition⟩ := S.wcaps.position _ htr
  unfold translatePosCode
  apply CAST
  have tmid : Q.cost (QS.elim (QS.inl (sum boundedRep kRep) msgRep)
      (Q.compose (QP.fst kRep (rep.ty scalar)) (Q.compose (QS.inr boundedRep kRep) (QS.inl (sum boundedRep kRep) msgRep))))
      pos ≤ 6 * tick := by
    rcases pos with l | m
    · have hl : Q.size (sum boundedRep kRep) l ≤ 3 * width := inl_payload S.sizes _ _ l hdec
      have t1 := INL (sum boundedRep kRep) msgRep l (by sz) (by exact hdec.trans (by sz))
      have := ELIML _ (Q.compose (QP.fst kRep (rep.ty scalar))
        (Q.compose (QS.inr boundedRep kRep) (QS.inl (sum boundedRep kRep) msgRep))) l t1
        (by exact hdec.trans (by sz)) (by exact hdec.trans (by sz))
      sz
    · have hm : Q.size msgRep m ≤ width := hpos
      have hm1 : Q.size kRep m.1 ≤ Q.size msgRep m := S.sizes.fst_le _ _ m
      have hin := inr_size S.sizes boundedRep kRep m.1 (by sz)
      have t1 := FST kRep (rep.ty scalar) m (by sz) (by sz)
      have t2 := INR boundedRep kRep m.1 (by sz) (by sz)
      have t3 := INL (sum boundedRep kRep) msgRep (Sum.inr m.1) (by sz) (by exact htr.trans (by sz))
      have t4 := COMPOSE _ _ m.1 t2 t3 (by sz) (by sz) (by exact htr.trans (by sz))
      have t5 := COMPOSE _ _ m t1 t4 (by sz) (by sz) (by exact htr.trans (by sz))
      have := ELIMR (QS.inl (sum boundedRep kRep) msgRep) _ m t5 (by exact hdec.trans (by sz)) (by exact htr.trans (by sz))
      sz
  have t6 := COMPOSE _ _ pos tmid hposition (by exact hdec.trans (by sz)) (by exact htr.trans (by sz))
    (by exact hbd'.trans h8)
  have := COMPOSE _ _ pos hreq t6 (by exact hbd.trans h8) (by exact hdec.trans (by sz)) (by exact hbd'.trans h8)
  sz

/-! ## The readout at each kind of state -/

omit S in
variable (rep) in
/-- What the wrapper knows about an attacker state it holds. -/
structure InnerState (width stateWidth headWidth work : Nat) (s : R.machine.State) : Prop where
  state : Q.size R.state s ≤ stateWidth
  head : Q.size bdI.head (R.machine.head s) ≤ headWidth
  headCost : Q.cost R.headCode s ≤ work
  request : ∀ i next, R.machine.view s = .inr ⟨i, next⟩ →
    WeightedAGM.NativeHandler.RequestSized (Q := Q) rep key Weights.syncMessage width i

/-- A returned value of a held attacker state is within its readout width. -/
theorem InnerState.output {s : R.machine.State} (hs : InnerState rep width stateWidth headWidth work s)
    (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hv : R.machine.view s = .inl result) :
    Q.size bdI.out result ≤ headWidth := by
  have := hs.head
  rw [R.machine.head_eq_inl_of_view hv] at this
  exact inl_payload S.sizes _ _ result this

/-- The size of the wrapper's exposed readout from an attacker readout. -/
theorem exposed_size (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s) :
    Q.size bdI.head (headReadyFn R s) ≤ 9 * width ∧ Q.size bdI.head (headGotFn R s) ≤ 9 * width := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  rcases hv : R.machine.view s with result | ⟨pos, next⟩
  · have hres := hs.output S result hv
    obtain ⟨hdec, _⟩ := S.wcaps.output result (hres.trans S.headRoute)
    have hkey := outputKey_size S result hdec
    obtain ⟨_, hbd⟩ := hashPos_size S _ hkey
    have h := inr_size S.sizes bdI.out bdI.pos _ hbd
    simp only [headReadyFn, headGotFn, R.machine.head_eq_inl_of_view hv, Sum.elim_inl]
    exact ⟨by change Q.size (sum bdI.out bdI.pos) _ ≤ _; sz, by change Q.size (sum bdI.out bdI.pos) _ ≤ _; sz⟩
  · have hpos := hs.request pos next hv
    have htr : Q.size (posRep rep) (translatePos pos) ≤ 3 * width :=
      WeightedAGM.NativeHandler.request_size rep key Weights.syncMessage S.sizes width hh _
        (translatePos_sized rep S.sizes width pos hpos)
    obtain ⟨hbd', _⟩ := S.wcaps.position _ htr
    obtain ⟨hbd, _⟩ := S.pcaps.request pos hpos
    have h1 := inr_size S.sizes bdI.out bdI.pos _ hbd'
    have h2 := inr_size S.sizes bdI.out bdI.pos _ hbd
    simp only [headReadyFn, headGotFn, R.machine.head_eq_inr_of_view hv, Sum.elim_inr]
    exact ⟨by change Q.size (sum bdI.out bdI.pos) _ ≤ _; sz, by change Q.size (sum bdI.out bdI.pos) _ ≤ _; sz⟩

/-- The relabeled readout of an attacker state. -/
theorem relabel_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s) :
    Q.cost (QS.elim (Q.compose (finalPosCode rep ports wports) (QS.inr bdI.out bdI.pos))
      (Q.compose (translatePosCode rep ports wports) (QS.inr bdI.out bdI.pos))) (R.machine.head s) ≤
      2 * adapterTime + 12 * tick ∧
    Q.cost (QS.elim (Q.compose (finalPosCode rep ports wports) (QS.inr bdI.out bdI.pos)) (QS.inr bdI.out bdI.pos))
      (R.machine.head s) ≤ 2 * adapterTime + 12 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hHF := route_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h8 := eight_width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h64 := room_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have hw := width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  rcases hv : R.machine.view s with result | ⟨pos, next⟩
  · have hres := hs.output S result hv
    obtain ⟨hdec, _⟩ := S.wcaps.output result (hres.trans S.headRoute)
    have hkey := outputKey_size S result hdec
    obtain ⟨_, hbd⟩ := hashPos_size S _ hkey
    have hsum := inr_size S.sizes bdI.out bdI.pos _ hbd
    have tf := finalPosCode_cost S result hres
    have ti := INR bdI.out bdI.pos _ (by exact hbd.trans h8) (by sz)
    have tc := COMPOSE _ _ result tf ti (by sz) (by exact hbd.trans h8) (by sz)
    have hhead : Q.size (sum bdI.out bdI.pos) (.inl result) ≤ WF := by
      have := hs.head; rw [R.machine.head_eq_inl_of_view hv] at this; sz
    rw [R.machine.head_eq_inl_of_view hv]
    have e1 := ELIML _ (Q.compose (translatePosCode rep ports wports) (QS.inr bdI.out bdI.pos)) result tc hhead (by sz)
    have e2 := ELIML _ (QS.inr bdI.out bdI.pos) result tc hhead (by sz)
    sz
  · have hpos := hs.request pos next hv
    have htr : Q.size (posRep rep) (translatePos pos) ≤ 3 * width :=
      WeightedAGM.NativeHandler.request_size rep key Weights.syncMessage S.sizes width hh _
        (translatePos_sized rep S.sizes width pos hpos)
    obtain ⟨hbd', _⟩ := S.wcaps.position _ htr
    obtain ⟨hbd, _⟩ := S.pcaps.request pos hpos
    have hsum := inr_size S.sizes bdI.out bdI.pos _ hbd'
    have hsum' := inr_size S.sizes bdI.out bdI.pos _ hbd
    have tt := translatePosCode_cost S pos hpos
    have ti := INR bdI.out bdI.pos _ (by exact hbd'.trans h8) (by sz)
    have ti' := INR bdI.out bdI.pos pos (by exact hbd.trans h8) (by sz)
    have tc := COMPOSE _ _ pos tt ti (by exact hbd.trans h8) (by exact hbd'.trans h8) (by sz)
    have hhead : Q.size (sum bdI.out bdI.pos) (.inr pos) ≤ WF := by
      have := hs.head; rw [R.machine.head_eq_inr_of_view hv] at this; sz
    rw [R.machine.head_eq_inr_of_view hv]
    have e1 := ELIMR (Q.compose (finalPosCode rep ports wports) (QS.inr bdI.out bdI.pos)) _ pos tc hhead (by sz)
    have e2 := ELIMR (Q.compose (finalPosCode rep ports wports) (QS.inr bdI.out bdI.pos)) _ pos ti' hhead (by sz)
    sz

theorem headReadyCode_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s)
    (marks : List (Mark F)) (hm : Q.size mRep marks ≤ marksWidth width (cap + 1)) :
    Q.cost (headReadyCode rep ports wports R) (s, marks) ≤ work + 2 * adapterTime + 15 * tick := by
  have hsh := hs.head
  have hss := hs.state
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hSF := inner_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have hHF := route_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h8 := eight_width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h64 := room_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have hready := ready_le_frame rep S.sizes R width cap stateWidth routeWidth outputWidth finishedRoute hh s hs.state marks hm
  obtain ⟨hexp, _⟩ := exposed_size S s hs
  obtain ⟨tmid, _⟩ := relabel_cost S s hs
  unfold headReadyCode
  apply CAST
  have t1 := FST R.state mRep (s, marks) (by change Q.size (readyRep rep R) (s, marks) ≤ _; sz) (by exact hs.state.trans hSF)
  have t2 := COMPOSE _ _ s hs.headCost tmid (hs.state.trans hSF) (by sz)
    (by change Q.size bdI.head (headReadyFn R s) ≤ _; sz)
  have := COMPOSE _ _ (s, marks) t1 t2 (by change Q.size (readyRep rep R) (s, marks) ≤ _; sz) (hs.state.trans hSF)
    (by change Q.size bdI.head (headReadyFn R s) ≤ _; sz)
  sz

theorem headGotCode_cost (s : R.machine.State) (hs : InnerState rep width stateWidth headWidth work s) (h : G₁)
    (marks : List (Mark F)) (hm : Q.size mRep marks ≤ marksWidth width (cap + 1)) :
    Q.cost (headGotCode rep ports wports R) (s, h, marks) ≤ work + 2 * adapterTime + 15 * tick := by
  have hsh := hs.head
  have hss := hs.state
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hSF := inner_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have hHF := route_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h8 := eight_width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h64 := room_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have hgot := got_le_frame rep S.sizes R width cap stateWidth routeWidth outputWidth finishedRoute hh S.point₁ s hs.state h marks hm
  obtain ⟨_, hexp⟩ := exposed_size S s hs
  obtain ⟨_, tmid⟩ := relabel_cost S s hs
  unfold headGotCode
  apply CAST
  have t1 := FST R.state (prod pRep mRep) (s, h, marks) (by change Q.size (gotRep rep R) (s, h, marks) ≤ _; sz)
    (by exact hs.state.trans hSF)
  have t2 := COMPOSE _ _ s hs.headCost tmid (hs.state.trans hSF) (by sz)
    (by change Q.size bdI.head (headGotFn R s) ≤ _; sz)
  have := COMPOSE _ _ (s, h, marks) t1 t2 (by change Q.size (gotRep rep R) (s, h, marks) ≤ _; sz) (hs.state.trans hSF)
    (by change Q.size bdI.head (headGotFn R s) ≤ _; sz)
  sz

/-- Decoding the returned output alongside the marks. -/
theorem decodeStage_cost (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hr : Q.size bdI.out result ≤ headWidth)
    (marks : List (Mark F)) (hm : Q.size mRep marks ≤ marksWidth width (cap + 1)) :
    Q.cost (QP.pair (Q.compose (QP.fst bdI.out mRep) wports.output) (QP.snd bdI.out mRep)) (result, marks) ≤
      adapterTime + 4 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  obtain ⟨hdec, hout⟩ := S.wcaps.output result (hr.trans S.headRoute)
  have hA := pair_size S.sizes bdI.out mRep result marks hr hm
  have hB := pair_size S.sizes (rep.ty OutTy) mRep result marks hdec hm
  have t1 := FST bdI.out mRep (result, marks) (by sz) (by sz)
  have t2 := COMPOSE _ _ (result, marks) t1 hout (by sz) (by sz) (by sz)
  have t3 := SND bdI.out mRep (result, marks) (by sz) (by sz)
  have := PAIR _ _ (result, marks) t2 t3 (by sz) (by sz)
  sz

/-- The final scalar of the decoded output. -/
theorem finalScalarCode_cost (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hdec : Q.size (rep.ty OutTy) result ≤ outputWidth)
    (marks : List (Mark F)) (hm : Q.size mRep marks ≤ marksWidth width (cap + 1)) :
    Q.cost (finalScalarCode rep correction finalFn keys code) (result, marks) ≤ routineTime + 4 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hf := S.fcaps.scalar
  have hmsg : Q.size msgRep result.1 ≤ Q.size (rep.ty OutTy) result := S.sizes.fst_le _ _ result
  have hfinal := S.scaps.fin result.1 (by sz)
  have hv := hf (finalFn result.1)
  have hB := pair_size S.sizes (rep.ty OutTy) mRep result marks hdec hm
  unfold finalScalarCode
  apply CAST
  have t4 := FST (rep.ty OutTy) mRep (result, marks) (by sz) (by sz)
  have t5 := FST msgRep restRep result (by sz) (by sz)
  have t6 := COMPOSE _ _ result t5 hfinal (by sz) (by sz) (by sz)
  have := COMPOSE _ _ (result, marks) t4 t6 (by sz) (by sz) (by sz)
  sz

/-- Assembling the finish arguments. -/
theorem finishArgsCode_cost (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hdec : Q.size (rep.ty OutTy) result ≤ outputWidth)
    (marks : List (Mark F)) (hm : Q.size mRep marks ≤ marksWidth width (cap + 1)) (v : F) :
    Q.cost (finishArgsCode rep data) ((result, marks), v) ≤ 11 * tick := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hu := S.fcaps.unit
  have hv := S.fcaps.scalar v
  have hB := pair_size S.sizes (rep.ty OutTy) mRep result marks hdec hm
  have hC := pair_size S.sizes (prod (rep.ty OutTy) mRep) (rep.ty scalar) (result, marks) v hB hv
  have hE2 := pair_size S.sizes (rep.ty scalar) (rep.env []) v () hv hu
  have hE1 := pair_size S.sizes mRep (rep.env [scalar]) marks (v, ()) hm hE2
  have hE0 := pair_size S.sizes (rep.ty OutTy) (rep.env [.list markTy, scalar]) result (marks, v, ()) hdec hE1
  unfold finishArgsCode
  apply CAST
  have a1 := FST (prod (rep.ty OutTy) mRep) (rep.ty scalar) ((result, marks), v) (by sz) (by sz)
  have a2 := FST (rep.ty OutTy) mRep (result, marks) (by sz) (by sz)
  have a3 := COMPOSE _ _ ((result, marks), v) a1 a2 (by sz) (by sz) (by sz)
  have a4 := SND (rep.ty OutTy) mRep (result, marks) (by sz) (by sz)
  have a5 := COMPOSE _ _ ((result, marks), v) a1 a4 (by sz) (by sz) (by sz)
  have a6 := SND (prod (rep.ty OutTy) mRep) (rep.ty scalar) ((result, marks), v) (by sz) (by sz)
  have a7 := UNITC (prod (prod (rep.ty OutTy) mRep) (rep.ty scalar)) ((result, marks), v) (by sz) (by sz)
  have a8 := PAIR _ _ ((result, marks), v) a6 a7 (by sz) (by sz)
  have a9 := PAIR _ _ ((result, marks), v) a5 a8 (by sz) (by sz)
  have := PAIR _ _ ((result, marks), v) a3 a9 (by sz) (by sz)
  sz

/-- The finish from a returned output and the recorded marks. -/
theorem finishCode_cost (result : OutTy.Value (cryptoBase F G₁ G₂ K M)) (hr : Q.size bdI.out result ≤ headWidth)
    (marks : List (Mark F)) (hml : marks.length ≤ cap) (hm : Q.size mRep marks ≤ marksWidth width (cap + 1)) :
    Q.cost (finishCode rep data cost primitive ports wports correction finalFn keys code) (result, marks) ≤
      2 * adapterTime + routineTime + finishTime overhead width cap outputWidth opTime + 25 * tick ∧
    Q.size bdI.out (fin finalFn result marks) ≤ finishedRoute := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hFW := finishedWidth_le_frame S
  obtain ⟨hdec, hout⟩ := S.wcaps.output result (hr.trans S.headRoute)
  have hfin := finished_size S result hdec marks hml
  obtain ⟨henc, hencode⟩ := S.wcaps.encode _ hfin
  have hv := S.fcaps.scalar (finalFn result.1)
  have hA := pair_size S.sizes bdI.out mRep result marks hr hm
  have hB := pair_size S.sizes (rep.ty OutTy) mRep result marks hdec hm
  have hC := pair_size S.sizes (prod (rep.ty OutTy) mRep) (rep.ty scalar) (result, marks) (finalFn result.1) hB hv
  have hE2 := pair_size S.sizes (rep.ty scalar) (rep.env []) (finalFn result.1) () hv hu
  have hE1 := pair_size S.sizes mRep (rep.env [scalar]) marks (finalFn result.1, ()) hm hE2
  have hE0 := pair_size S.sizes (rep.ty OutTy) (rep.env [.list markTy, scalar]) result (marks, finalFn result.1, ()) hdec hE1
  have hfinW : Q.size (rep.ty OutTy) (fin finalFn result marks) ≤ WF := hfin.trans hFW
  have hencW : Q.size bdI.out (fin finalFn result marks) ≤ WF :=
    henc.trans (finished_le_frame width cap stateWidth routeWidth outputWidth finishedRoute)
  have tdec := decodeStage_cost S result hr marks hm
  have tfs := finalScalarCode_cost S result hdec marks hm
  have targs := finishArgsCode_cost S result hdec marks hm (finalFn result.1)
  have tcompile := finish_cost rep data cost primitive S.laws S.dataLaws primitiveBound S.sizes S.lists S.mono S.fcaps S.lens
    result marks (finalFn result.1) hdec hml
  have hden : finExpr.denote (arithmetic F G₁ G₂ K M cost) (result, marks, finalFn result.1, ()) = fin finalFn result marks :=
    finExpr_denote_fin cost finalFn result marks
  have hencode' : Q.cost wports.encode (finExpr.denote (arithmetic F G₁ G₂ K M cost) (result, marks, finalFn result.1, ())) ≤
      adapterTime := by rw [hden]; exact hencode
  refine ⟨?_, henc⟩
  unfold finishCode
  apply CAST
  have tid := IDENT (prod (rep.ty OutTy) mRep) (result, marks) (by sz)
  have tpair := PAIR _ _ (result, marks) tid tfs (by sz) (by sz)
  have tenc := COMPOSE _ _ (result, marks, finalFn result.1, ()) tcompile hencode' (by sz) (by rw [hden]; exact hfinW)
    (by (try dsimp only [Function.comp_def, id]); rw [hden]; exact hencW)
  have tfinish := COMPOSE _ _ ((result, marks), finalFn result.1) targs tenc (by sz) (by sz) (by (try dsimp only [Function.comp_def, id]); rw [hden]; exact hencW)
  have tbody := COMPOSE _ _ (result, marks) tpair tfinish (by sz) (by sz) (by (try dsimp only [Function.comp_def, id]); rw [hden]; exact hencW)
  have := COMPOSE _ _ (result, marks) tdec tbody (by sz) (by sz) (by (try dsimp only [Function.comp_def, id]); rw [hden]; exact hencW)
  sz

omit S in
/-- The readout budget of the wrapper. -/
def headTime (overhead : Nat → Nat) (width cap stateWidth routeWidth outputWidth finishedRoute adapterTime routineTime
    opTime work : Nat) : Nat :=
  work + 2 * adapterTime + routineTime + finishTime overhead width cap outputWidth opTime +
    29 * fee overhead (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)

omit S in
variable (rep) in
/-- A wrapper state the wrapper can be in: bounded attacker state and marks, a held point, or a
returned output with its marks. -/
inductive WrapState (width cap stateWidth headWidth work : Nat) : State R.machine (F := F) → Prop
  | ready {s : R.machine.State} {marks : List (Mark F)} (hs : InnerState rep width stateWidth headWidth work s)
      (hml : marks.length ≤ cap) : WrapState width cap stateWidth headWidth work (ready R.machine s marks)
  | gotHash {s : R.machine.State} {h : G₁} {marks : List (Mark F)} (hs : InnerState rep width stateWidth headWidth work s)
      (hml : marks.length ≤ cap) : WrapState width cap stateWidth headWidth work (gotHash R.machine s h marks)
  | done {result : OutTy.Value (cryptoBase F G₁ G₂ K M)} {marks : List (Mark F)} (hr : Q.size bdI.out result ≤ headWidth)
      (hml : marks.length ≤ cap) : WrapState width cap stateWidth headWidth work (done R.machine result marks)

theorem headCode_cost (st : State R.machine (F := F)) (hst : WrapState rep width cap stateWidth headWidth work st) :
    Q.cost (headCode rep data cost primitive ports wports correction finalFn keys code R) st ≤
      headTime overhead width cap stateWidth routeWidth outputWidth finishedRoute adapterTime routineTime opTime work ∧
    Q.size (outerBoundary rep (bdI := bdI)).head ((wrapped correction finalFn keys R).head st) ≤ 9 * width + finishedRoute := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hw := width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h8 := eight_width_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have h64 := room_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have hFF := finished_le_frame width cap stateWidth routeWidth outputWidth finishedRoute
  have hfn := congrFun (headFn_eq correction finalFn keys R) st
  rw [← hfn]
  unfold headCode headTime
  rcases hst with @⟨s, marks, hs, hml⟩ | @⟨s, h, marks, hs, hml⟩ | @⟨result, marks, hr, hml⟩
  · have hm : Q.size mRep marks ≤ marksWidth width (cap + 1) :=
      (marks_size rep S.sizes S.lists width cap hh S.fcaps.bool S.fcaps.scalar marks hml).trans (marksWidth_le_succ width cap)
    have hready := ready_le_frame rep S.sizes R width cap stateWidth routeWidth outputWidth finishedRoute hh s hs.state marks hm
    obtain ⟨hexp, _⟩ := exposed_size S s hs
    have t := headReadyCode_cost S s hs marks hm
    refine ⟨?_, by change Q.size bdI.head (headReadyFn R s) ≤ _; sz⟩
    apply CAST
    have hsum := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (s, marks) le_rfl
    have := ELIML _ (QS.elim (headGotCode rep ports wports R)
        (headDoneCode rep data cost primitive ports wports correction finalFn keys code)) (s, marks) t
      (by change Q.size (stateRep rep R) (ready R.machine s marks) ≤ _; sz)
      (by change Q.size bdI.head (headReadyFn R s) ≤ _; sz)
    sz
  · have hm : Q.size mRep marks ≤ marksWidth width (cap + 1) :=
      (marks_size rep S.sizes S.lists width cap hh S.fcaps.bool S.fcaps.scalar marks hml).trans (marksWidth_le_succ width cap)
    have hgot := got_le_frame rep S.sizes R width cap stateWidth routeWidth outputWidth finishedRoute hh S.point₁ s hs.state h marks hm
    obtain ⟨_, hexp⟩ := exposed_size S s hs
    have t := headGotCode_cost S s hs h marks hm
    refine ⟨?_, by change Q.size bdI.head (headGotFn R s) ≤ _; sz⟩
    apply CAST
    have hin := inl_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (s, h, marks) le_rfl
    have hsum := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (Sum.inl (s, h, marks)) hin
    have e1 := ELIML _ (headDoneCode rep data cost primitive ports wports correction finalFn keys code) (s, h, marks) t
      (by sz) (by change Q.size bdI.head (headGotFn R s) ≤ _; sz)
    have := ELIMR (headReadyCode rep ports wports R) _ (Sum.inl (s, h, marks)) e1
      (by change Q.size (stateRep rep R) (gotHash R.machine s h marks) ≤ _; sz)
      (by change Q.size bdI.head (headGotFn R s) ≤ _; sz)
    sz
  · have hm : Q.size mRep marks ≤ marksWidth width (cap + 1) :=
      (marks_size rep S.sizes S.lists width cap hh S.fcaps.bool S.fcaps.scalar marks hml).trans (marksWidth_le_succ width cap)
    have hdone := done_le_frame rep S.sizes width cap stateWidth headWidth routeWidth outputWidth finishedRoute hh hHR result hr marks hm
    obtain ⟨t, henc⟩ := finishCode_cost S result hr marks hml hm
    have hsumout := inl_size S.sizes bdI.out bdI.pos (fin finalFn result marks) henc
    refine ⟨?_, by change Q.size (sum bdI.out bdI.pos) (.inl (fin finalFn result marks)) ≤ _; sz⟩
    apply CAST
    have hin := inr_size S.sizes (gotRep rep R) (doneRep rep (bdI := bdI)) (result, marks) le_rfl
    have hsum := inr_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (Sum.inr (result, marks)) hin
    have tdone : Q.cost (headDoneCode rep data cost primitive ports wports correction finalFn keys code) (result, marks) ≤
        2 * adapterTime + routineTime + finishTime overhead width cap outputWidth opTime + 27 * tick := by
      unfold headDoneCode
      apply CAST
      have ti := INL bdI.out bdI.pos (fin finalFn result marks) (by sz) (by sz)
      have := COMPOSE _ _ (result, marks) t ti (by change Q.size (doneRep rep (bdI := bdI)) (result, marks) ≤ _; sz)
        (by sz) (by sz)
      sz
    have e1 := ELIMR (headGotCode rep ports wports R) _ (result, marks) tdone (by sz) (by sz)
    have := ELIMR (headReadyCode rep ports wports R) _ (Sum.inr (result, marks)) e1
      (by change Q.size (stateRep rep R) (done R.machine result marks) ≤ _; sz) (by sz)
    sz

/-! ## Initialization -/

omit S in
/-- The initialization budget of the wrapper. -/
def initTime (overhead : Nat → Nat) (width cap stateWidth routeWidth outputWidth finishedRoute adapterTime routineTime
    initWork : Nat) : Nat :=
  initWork + routineTime + adapterTime + 8 * fee overhead (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)

theorem initCode_cost (pk : G₂) (initWork : Nat) (hinit : Q.cost R.initCode (keys pk) ≤ initWork)
    (hstate : Q.size R.state (R.machine.init (keys pk)) ≤ stateWidth) :
    Q.cost (initCode rep data ports wports correction finalFn keys code R) pk ≤
      initTime overhead width cap stateWidth routeWidth outputWidth finishedRoute adapterTime routineTime initWork := by
  have hh := S.fcaps.hdr
  have hOK := S.outputKey
  have hHR := S.headRoute
  have hu := S.fcaps.unit
  have hpk := S.point₂ pk
  obtain ⟨hkeys, tkeys⟩ := S.scaps.keys pk hpk
  obtain ⟨hinput, tinput⟩ := S.wcaps.input (keys pk) hkeys
  have hnil : Q.size mRep [] ≤ header := S.lists.nil_le _
  have hmw : header ≤ marksWidth width (cap + 1) := by unfold marksWidth; nlinarith
  have hready := ready_le_frame rep S.sizes R width cap stateWidth routeWidth outputWidth finishedRoute hh _ hstate [] (hnil.trans hmw)
  have hsum := inl_size S.sizes (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (R.machine.init (keys pk), []) le_rfl
  unfold initCode initTime
  apply CAST
  have t1 := COMPOSE _ _ (keys pk) tinput hinit (by sz) (by sz) (by sz)
  have t2 := COMPOSE _ _ pk tkeys t1 (by sz) (by sz) (by sz)
  have t3 := UNITC (rep.ty point₂) pk (by sz) (by sz)
  have t4 := FrameCost.nil_le S.dataLaws S.mono (wrapFrame width cap stateWidth routeWidth outputWidth finishedRoute)
    (rep.ty markTy) (by sz) (by sz)
  have t5 := COMPOSE _ _ pk t3 t4 (by sz) (by sz) (by sz)
  have t6 := PAIR _ _ pk t2 t5 (by sz) (by sz)
  have t7 := INL (readyRep rep R) (sum (gotRep rep R) (doneRep rep (bdI := bdI))) (R.machine.init (keys pk), []) (by sz) (by sz)
  have := COMPOSE _ _ pk t6 t7 (by sz) (by sz) (by sz)
  sz

end Signatures.Runtime.SyncWrapGeneral
