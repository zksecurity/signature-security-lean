import Proofs.Runtime.BackendSchnorrAGMHandlerPorts
import Proofs.Runtime.BackendRetainedTagBudget

/-! The actual indexed Schnorr dispatcher adds request retention, implemented
reply tagging, nested sum routing and request decoding to the three component
budgets. One call reserves at most one extra cell in each state capacity. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

def handlerTime (overhead : Nat → Nat) (frameWidth randomTime hashTime signingTime requestTime tagTime : Nat) : Nat :=
  max randomTime (max hashTime signingTime) + requestTime + tagTime + 40 * overhead (128 * frameWidth)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input Output : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include sizes lists laws mono routing dispatchLaws

theorem code_bound_of_components
    (width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth requestTime tagTime randomTime hashTime signingTime : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (caps : PortCaps rep bd ports width groupCap rowCap coeffCap arityCap portWidth requestTime tagTime)
    (hrandom : Bounds control queryCost (HandlerComponents.random rep data cost primitive randomPorts)
      (fun input => HandlerComponents.Input (Q := Q) rep .nat width cap basisCap signedCap groupCap rowCap coeffCap input ∧ input.1.1 ≤ arityCap)
      (fun output => HandlerComponents.Output (Q := Q) rep .nat width cap basisCap signedCap output ∧ output.1.1 ≤ arityCap) randomTime)
    (hhash : Bounds control queryCost (HandlerComponents.hash rep data cost primitive sampler)
      (HandlerComponents.Input (Q := Q) rep message width cap basisCap signedCap groupCap rowCap coeffCap)
      (HandlerComponents.Output (Q := Q) rep scalar width (cap + 1) basisCap signedCap) hashTime)
    (hsigning : Bounds control queryCost (HandlerComponents.signing rep data cost primitive sampler)
      (HandlerComponents.Input (Q := Q) rep message width cap basisCap signedCap groupCap rowCap coeffCap)
      (HandlerComponents.Output (Q := Q) rep scalar width (cap + 1) (basisCap + 1) (signedCap + 1)) signingTime) :
    Bounds control queryCost (code rep bd ports data cost primitive randomPorts sampler)
      (fun input => RequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap input.1 ∧
        HandlerComponents.StoreBound (Q := Q) rep width cap basisCap signedCap input.2)
      (fun output => Q.size bd.idx output.1 ≤ portWidth ∧
        HandlerComponents.StoreBound (Q := Q) rep width (cap + 1) (basisCap + 1) (signedCap + 1) output.2)
      (handlerTime overhead (frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth)
        randomTime hashTime signingTime requestTime tagTime) := by
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth
  let fee := overhead (128 * W)
  let pre := HandlerComponents.StoreBound (Q := Q) rep width cap basisCap signedCap
  let post := HandlerComponents.StoreBound (Q := Q) rep width (cap + 1) (basisCap + 1) (signedCap + 1)
  let reqR := RandomArgsBound (Q := Q) rep width groupCap rowCap coeffCap arityCap
  let reqG := HandlerComponents.ArgsBound (Q := Q) rep message width groupCap rowCap coeffCap
  let replyR := fun r : Nat × List G₁ => ReplyBound (Q := Q) rep .nat width r ∧ r.1 ≤ arityCap
  let replyG := ReplyBound (Q := Q) rep scalar width
  have hw := frame_widths width cap basisCap signedCap groupCap rowCap coeffCap portWidth
  have hpost (s) (hs : post s) : Q.size (rep.ty storeTy) s ≤ W :=
    store_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap portWidth hh hb hf s hs
  have hpre (s) (hs : pre s) : Q.size (rep.ty storeTy) s ≤ W :=
    hpost s (HandlerComponents.store_mono rep width cap basisCap signedCap (cap + 1) (basisCap + 1) (signedCap + 1)
      (by omega) (by omega) (by omega) s hs)
  have hreqR (args) (ha : reqR args) : Q.size (rep.ty randomArgsTy) args ≤ W :=
    args_size rep sizes lists .nat width cap basisCap signedCap groupCap rowCap coeffCap portWidth hh hf hg args ha.1
  have hreqG (args) (ha : reqG args) : Q.size (rep.ty groupArgsTy) args ≤ W :=
    args_size rep sizes lists message width cap basisCap signedCap groupCap rowCap coeffCap portWidth hh hf hg args ha
  have hreplyR (r) (hr : replyR r) : Q.size (rep.ty (groupReplyTy .nat)) r ≤ W :=
    (reply_size rep sizes lists .nat width hh r hr.1).trans (by omega)
  have hreplyG (r) (hr : replyG r) : Q.size (rep.ty scalarGroupReplyTy) r ≤ W :=
    (reply_size rep sizes lists scalar width hh r hr).trans (by omega)
  let preR := fun p : Interface.Args Nat F G₁ × ((G₁ × G₁) × EncodedState F G₁ M) => reqR p.1 ∧ pre p.2
  let preG := fun p : Interface.Args M F G₁ × ((G₁ × G₁) × EncodedState F G₁ M) => reqG p.1 ∧ pre p.2
  let final := fun p : SourceIndex F G₁ M × ((G₁ × G₁) × EncodedState F G₁ M) => Q.size bd.idx p.1 ≤ portWidth ∧ post p.2
  have hr : Bounds control queryCost (random rep bd ports data cost primitive randomPorts)
      preR final (randomTime + tagTime + 26 * fee) := by
    apply retainedTag_bound_of_width sizes laws mono control queryCost routing
      (rep.ty randomArgsTy) (rep.ty (groupReplyTy .nat)) bd.idx (rep.ty storeTy) ports.randomTag
      (HandlerComponents.random rep data cost primitive randomPorts) reqR replyR pre post W portWidth tagTime randomTime
      (by omega) hw.2.1 hreqR hreplyR hpre hpost
    · intro args r ha hr
      exact caps.randomTag args r ha hr.1 hr.2
    · intro input hi out hout
      obtain ⟨ho, ht⟩ := hrandom input ⟨⟨hi.1.1, hi.2⟩, hi.1.2⟩ out hout
      exact ⟨⟨⟨⟨ho.1.data, ho.1.groups, ho.1.groupLength⟩, ho.2⟩,
        HandlerComponents.store_mono rep width cap basisCap signedCap (cap + 1) (basisCap + 1) (signedCap + 1)
          (by omega) (by omega) (by omega) _ ho.1.store⟩, ht⟩
  have hgb (signing : Bool) : Bounds control queryCost (groupCode rep data cost primitive sampler signing)
      preG (fun p => replyG p.1 ∧ post p.2) (max hashTime signingTime) := by
    intro input hi out hout
    cases signing with
    | false =>
        obtain ⟨ho, ht⟩ := hhash input hi out hout
        exact ⟨⟨⟨ho.data, ho.groups, ho.groupLength⟩,
          HandlerComponents.store_mono rep width (cap + 1) basisCap signedCap (cap + 1) (basisCap + 1) (signedCap + 1)
            le_rfl (by omega) (by omega) _ ho.store⟩, ht.trans (Nat.le_max_left _ _)⟩
    | true =>
        obtain ⟨ho, ht⟩ := hsigning input hi out hout
        exact ⟨⟨⟨ho.data, ho.groups, ho.groupLength⟩, ho.store⟩, ht.trans (Nat.le_max_right _ _)⟩
  have hg' (signing : Bool) : Bounds control queryCost (group rep bd ports data cost primitive sampler signing)
      preG final (max hashTime signingTime + tagTime + 26 * fee) :=
    retainedTag_bound_of_width sizes laws mono control queryCost routing
      (rep.ty groupArgsTy) (rep.ty scalarGroupReplyTy) bd.idx (rep.ty storeTy) (ports.scalarTag signing)
      (groupCode rep data cost primitive sampler signing) reqG replyG pre post W portWidth tagTime (max hashTime signingTime)
      (by omega) hw.2.1 hreqG hreplyG hpre hpost (caps.scalarTag signing) (hgb signing)
  let preI := fun p : (Interface.Args M F G₁ ⊕ Interface.Args M F G₁) × ((G₁ × G₁) × EncodedState F G₁ M) =>
    Sum.elim (fun args => preG (args, p.2)) (fun args => preG (args, p.2)) p.1
  have hi : Bounds control queryCost (inner rep bd ports data cost primitive sampler)
      preI final (max hashTime signingTime + tagTime + 30 * fee) := by
    have h := branchStore_bound_of_width sizes mono control queryCost routing dispatchLaws (rep.ty storeTy)
      (group rep bd ports data cost primitive sampler false) (group rep bd ports data cost primitive sampler true)
      preG preG final (4 * W) _ _ (by omega)
      (fun p hp => ⟨(hreqG p.1 hp.1).trans (by omega), (hpre p.2 hp.2).trans (by omega)⟩)
      (fun p hp => ⟨(hreqG p.1 hp.1).trans (by omega), (hpre p.2 hp.2).trans (by omega)⟩) (hg' false) (hg' true)
    intro input hp out hout
    obtain ⟨ho, ht⟩ := h input hp out hout
    have heq : 32 * (4 * W) = 128 * W := by omega
    exact ⟨ho, by simp only [max_self, heq] at ht; dsimp only [fee] at *; omega⟩
  have hinnerSize (p) (hp : preI p) :
      Q.size (StepClass.HasSum.sum (rep.ty groupArgsTy) (rep.ty groupArgsTy)) p.1 ≤ 4 * W ∧
      Q.size (rep.ty storeTy) p.2 ≤ 4 * W := by
    rcases p with ⟨args | args, saved⟩
    · have ha := hreqG args hp.1
      have hs := hpre saved hp.2
      have hsum := sizes.sum_le (rep.ty groupArgsTy) (rep.ty groupArgsTy) (.inl args)
      dsimp only [Sum.elim] at hsum
      dsimp only
      exact ⟨by omega, by omega⟩
    · have ha := hreqG args hp.1
      have hs := hpre saved hp.2
      have hsum := sizes.sum_le (rep.ty groupArgsTy) (rep.ty groupArgsTy) (.inr args)
      dsimp only [Sum.elim] at hsum
      dsimp only
      exact ⟨by omega, by omega⟩
  let preO := fun p : NativeRequest F G₁ M × ((G₁ × G₁) × EncodedState F G₁ M) =>
    Sum.elim (fun args => preR (args, p.2)) (fun args => preI (args, p.2)) p.1
  have ho : Bounds control queryCost (dispatch rep bd ports data cost primitive randomPorts sampler)
      preO final (max (randomTime + tagTime + 26 * fee) (max hashTime signingTime + tagTime + 30 * fee) + 4 * fee) := by
    simpa only [dispatch, positions, preO, fee, ← Nat.mul_assoc, Nat.reduceMul] using
      branchStore_bound_of_width sizes mono control queryCost routing dispatchLaws (rep.ty storeTy)
        (random rep bd ports data cost primitive randomPorts) (inner rep bd ports data cost primitive sampler)
        preR preI final (4 * W) _ _ (by omega)
        (fun p hp => ⟨(hreqR p.1 hp.1).trans (by omega), (hpre p.2 hp.2).trans (by omega)⟩)
        hinnerSize hr hi
  have hnsize (q) (hq : NativeRequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap q) :
      Q.size (positions rep) q ≤ W :=
    (nativeRequest_size rep sizes lists width groupCap rowCap coeffCap arityCap hh hf hg q hq).trans hw.2.2.1
  have he := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing (rep.ty storeTy) ports.request
    (RequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap)
    (NativeRequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap) pre W requestTime
    (fun q hq => (caps.request q hq).1.trans hw.2.1) hpre
    (fun q hq => ⟨hq, hnsize (encodeRequest q) hq, (caps.request q hq).2⟩)
  have hpreO (p : NativeRequest F G₁ M × ((G₁ × G₁) × EncodedState F G₁ M))
      (hp : NativeRequestBound (Q := Q) rep width groupCap rowCap coeffCap arityCap p.1 ∧ pre p.2) : preO p := by
    rcases p with ⟨args | args | args, saved⟩ <;> exact hp
  intro input hp out hout
  simp only [code, Code.run, sequenceRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hout
  obtain ⟨mid, hm, result, hr', rfl⟩ := hout
  obtain ⟨hmid, hetime⟩ := he input hp mid hm
  obtain ⟨hresult, htime⟩ := ho mid.value (hpreO mid.value hmid) result hr'
  have hin := sizes.prod_le bd.pos (rep.ty storeTy) input
  have hmSize := sizes.prod_le (positions rep) (rep.ty storeTy) mid.value
  have hiq := (caps.request input.1 hp.1).1
  have his := hpre input.2 hp.2
  have hmq := hnsize mid.value.1 hmid.1
  have hms := hpre mid.value.2 hmid.2
  have hseq := routing.sequence (Q.size (StepClass.HasProd.prod bd.pos (rep.ty storeTy)) input)
    (Q.size (StepClass.HasProd.prod (positions rep) (rep.ty storeTy)) mid.value)
  have hfee := mono (show Q.size (StepClass.HasProd.prod bd.pos (rep.ty storeTy)) input +
      Q.size (StepClass.HasProd.prod (positions rep) (rep.ty storeTy)) mid.value ≤ 128 * W by omega)
  have hsmall := mono (show 32 * W ≤ 128 * W by omega)
  exact ⟨hresult, by dsimp only [handlerTime, fee, W] at *; omega⟩

end Signatures.Runtime.SchnorrAGM.Native.Handler
