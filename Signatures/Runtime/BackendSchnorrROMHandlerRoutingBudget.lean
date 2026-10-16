import Signatures.Runtime.BackendSchnorrROMHandlerPorts
import Signatures.Runtime.BackendRetainedTagBudget

/-! Full indexed ROM routing cost: retain the actual request, run its certified
component, tag the dependent reply, and execute both sum dispatches. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

open BackendProgram NativeInterface NativeComponents

def handlerTime (overhead : Nat → Nat) (width randomTime hashTime signingTime requestTime tagTime : Nat) : Nat :=
  max (max randomTime hashTime) signingTime + requestTime + tagTime + 40 * overhead (128 * width)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input Output : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : RawTape.NativePrivate.Ports (Q := Q) rep (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include sizes lists laws mono routing dispatchLaws

/-- Routing works for any executed signer with its proved component bound. -/
theorem codeWithSigning_bound_of_components
    (signer : Code Q unifSpec iface (rep.ty (withStore message)) (rep.ty (withStore signatureTy)))
    (width tapeWidth mc lc sc rc nextSavedCap arityCap portWidth requestTime tagTime randomTime hashTime signingTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hs : sc ≤ nextSavedCap)
    (hw : (6 * (nextSavedCap + rc) + 3) * tapeWidth ≤ width)
    (hNat : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ tapeWidth)
    (caps : PortCaps rep bd ports width tapeWidth arityCap portWidth requestTime tagTime)
    (hrandom : Bounds control queryCost (NativeComponents.random rep data cost primitive uniform)
      (fun p => p.1 ≤ arityCap ∧ StoreBound (Q := Q) rep width tapeWidth mc lc sc rc p.2)
      (InputBound (Q := Q) rep .nat tapeWidth width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc) randomTime)
    (hhash : Bounds control queryCost (NativeComponents.hash rep data cost primitive sampler)
      (InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth mc lc sc rc)
      (InputBound (Q := Q) rep scalar (3 * width) width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc) hashTime)
    (hsigning : Bounds control queryCost signer
      (InputBound (Q := Q) rep message width width tapeWidth mc lc sc rc)
      (InputBound (Q := Q) rep signatureTy (3 * width) width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc) signingTime) :
    Bounds control queryCost (codeWithSigning rep bd ports data cost primitive uniform sampler signer)
      (fun p => RequestBound (Q := Q) rep width arityCap p.1 ∧ StoreBound (Q := Q) rep width tapeWidth mc lc sc rc p.2)
      (fun p => Q.size bd.idx p.1 ≤ portWidth ∧ StoreBound (Q := Q) rep width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc p.2)
      (handlerTime overhead (frameWidth width mc lc portWidth) randomTime hashTime signingTime requestTime tagTime) := by
  let W := frameWidth width mc lc portWidth
  let fee := overhead (128 * W)
  let pre := StoreBound (Q := Q) rep width tapeWidth mc lc sc rc
  let post := StoreBound (Q := Q) rep width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc
  let reqR := fun n : Nat => n ≤ arityCap
  let reqH := fun k : M × G₁ => Q.size (rep.ty hashKey) k ≤ 3 * width
  let reqS := fun msg : M => Q.size (rep.ty message) msg ≤ width
  let replyR := fun r : Nat => Q.size rep.data.nat r ≤ tapeWidth
  let replyH := fun c : F => Q.size (rep.ty scalar) c ≤ 3 * width
  let replyS := fun sig : G₁ × F => Q.size (rep.ty signatureTy) sig ≤ 3 * width
  let preR := fun p : Nat × Shared.Store F G₁ M => reqR p.1 ∧ pre p.2
  let preH := fun p : (M × G₁) × Shared.Store F G₁ M => reqH p.1 ∧ pre p.2
  let preS := fun p : M × Shared.Store F G₁ M => reqS p.1 ∧ pre p.2
  let final := fun p : Response F G₁ M × Shared.Store F G₁ M => Q.size bd.idx p.1 ≤ portWidth ∧ post p.2
  have hW := frame_widths width mc lc portWidth
  have htw : tapeWidth ≤ width := by nlinarith only [hw, Nat.zero_le ((nextSavedCap + rc) * tapeWidth)]
  have hpost (s) (h : post s) : Q.size (rep.ty storeTy) s ≤ W :=
    store_size rep sizes lists width tapeWidth mc lc nextSavedCap rc portWidth hh ht hw s h
  have hpre (s) (h : pre s) : Q.size (rep.ty storeTy) s ≤ W :=
    hpost s (store_mono rep width tapeWidth mc lc sc rc (mc + 1) (lc + 1) nextSavedCap rc
      (by omega) (by omega) hs le_rfl s h)
  have hreqR (n) (h : reqR n) : Q.size rep.data.nat n ≤ W := (hNat n h).trans (by omega)
  have hreqH (k) (h : reqH k) : Q.size (rep.ty hashKey) k ≤ W := h.trans (by omega)
  have hreqS (msg) (h : reqS msg) : Q.size (rep.ty message) msg ≤ W := h.trans (by omega)
  have hr : Bounds control queryCost (random rep bd ports data cost primitive uniform)
      preR final (randomTime + tagTime + 26 * fee) :=
    retainedTag_bound_of_width sizes laws mono control queryCost routing rep.data.nat rep.data.nat bd.idx
      (rep.ty storeTy) ports.randomTag (NativeComponents.random rep data cost primitive uniform)
      reqR replyR pre post W portWidth tagTime randomTime (by omega) hW.2.1 hreqR
      (fun r h => h.trans (by omega)) hpre hpost caps.randomTag hrandom
  have hh' : Bounds control queryCost (hash rep bd ports data cost primitive sampler)
      preH final (hashTime + tagTime + 26 * fee) :=
    retainedTag_bound_of_width sizes laws mono control queryCost routing (rep.ty hashKey) (rep.ty scalar) bd.idx
      (rep.ty storeTy) ports.hashTag (NativeComponents.hash rep data cost primitive sampler)
      reqH replyH pre post W portWidth tagTime hashTime (by omega) hW.2.1 hreqH
      (fun c h => h.trans (by omega)) hpre hpost caps.hashTag hhash
  have hsign : Bounds control queryCost (tagged rep bd ports.signingTag signer)
      preS final (signingTime + tagTime + 26 * fee) :=
    retainedTag_bound_of_width sizes laws mono control queryCost routing (rep.ty message) (rep.ty signatureTy) bd.idx
      (rep.ty storeTy) ports.signingTag signer
      reqS replyS pre post W portWidth tagTime signingTime (by omega) hW.2.1 hreqS
      (fun sig h => h.trans (by omega)) hpre hpost caps.signingTag hsigning
  let preI := fun p : (Nat ⊕ (M × G₁)) × Shared.Store F G₁ M =>
    Sum.elim (fun n => preR (n, p.2)) (fun k => preH (k, p.2)) p.1
  have hi : Bounds control queryCost (inner rep bd ports data cost primitive uniform sampler)
      preI final (max randomTime hashTime + tagTime + 30 * fee) := by
    have h := branchStore_bound_of_width sizes mono control queryCost routing dispatchLaws (rep.ty storeTy)
      (random rep bd ports data cost primitive uniform) (hash rep bd ports data cost primitive sampler)
      preR preH final (4 * W) _ _ (by omega)
      (fun p h => ⟨(hreqR p.1 h.1).trans (by omega), (hpre p.2 h.2).trans (by omega)⟩)
      (fun p h => ⟨(hreqH p.1 h.1).trans (by omega), (hpre p.2 h.2).trans (by omega)⟩) hr hh'
    exact Bounds.time_mono control queryCost h (by simp only [← Nat.mul_assoc, Nat.reduceMul]; dsimp only [fee]; omega)
  have hinnerSize (p) (h : preI p) :
      Q.size (StepClass.HasSum.sum rep.data.nat (rep.ty hashKey)) p.1 ≤ 4 * W ∧ Q.size (rep.ty storeTy) p.2 ≤ 4 * W := by
    rcases p with ⟨n | k, saved⟩
    · have ha := hreqR n h.1
      have hs' := hpre saved h.2
      have hsum := sizes.sum_le rep.data.nat (rep.ty hashKey) (.inl n)
      dsimp only [Sum.elim] at hsum
      dsimp only
      exact ⟨by omega, by omega⟩
    · have ha := hreqH k h.1
      have hs' := hpre saved h.2
      have hsum := sizes.sum_le rep.data.nat (rep.ty hashKey) (.inr k)
      dsimp only [Sum.elim] at hsum
      dsimp only
      exact ⟨by omega, by omega⟩
  let preO := fun p : NativeInterface.Request G₁ M × Shared.Store F G₁ M =>
    Sum.elim (fun args => preI (args, p.2)) (fun msg => preS (msg, p.2)) p.1
  have ho : Bounds control queryCost (dispatchWithSigning rep bd ports data cost primitive uniform sampler signer)
      preO final (max (max randomTime hashTime) signingTime + tagTime + 34 * fee) := by
    have h := branchStore_bound_of_width sizes mono control queryCost routing dispatchLaws (rep.ty storeTy)
      (inner rep bd ports data cost primitive uniform sampler) (tagged rep bd ports.signingTag signer)
      preI preS final (4 * W) _ _ (by omega) hinnerSize
      (fun p h => ⟨(hreqS p.1 h.1).trans (by omega), (hpre p.2 h.2).trans (by omega)⟩) hi hsign
    exact Bounds.time_mono control queryCost h (by simp only [← Nat.mul_assoc, Nat.reduceMul]; dsimp only [fee]; omega)
  let sourcePre := fun p : NativeInterface.Request G₁ M × Shared.Store F G₁ M =>
    RequestBound (Q := Q) rep width arityCap p.1 ∧ pre p.2
  have hnsize (q) (hq : RequestBound (Q := Q) rep width arityCap q) : Q.size (positions rep) q ≤ W :=
    (nativeRequest_size rep sizes width tapeWidth arityCap hh htw hNat q hq).trans (by omega)
  have he := firstAtomic_bound_of_width (iface := iface) mono control queryCost routing (rep.ty storeTy) ports.request
    (RequestBound (Q := Q) rep width arityCap) (RequestBound (Q := Q) rep width arityCap) pre W requestTime
    (fun q h => (caps.request q h).1.trans hW.2.1) hpre
    (fun q h => ⟨h, hnsize q h, (caps.request q h).2⟩)
  have hd : Bounds control queryCost (dispatchWithSigning rep bd ports data cost primitive uniform sampler signer)
      sourcePre final (max (max randomTime hashTime) signingTime + tagTime + 34 * fee) := by
    apply Bounds.consequence control queryCost ho ?_ (fun _ h => h)
    rintro ⟨(n | k) | msg, saved⟩ h <;> exact h
  have hsrc (p) (h : sourcePre p) : Q.size (StepClass.HasProd.prod bd.pos (rep.ty storeTy)) p ≤ 4 * W := by
    have hq := (caps.request p.1 h.1).1.trans hW.2.1
    have hs' := hpre p.2 h.2
    exact (sizes.prod_le _ _ p).trans (by omega)
  have hnat (p) (h : sourcePre p) : Q.size (StepClass.HasProd.prod (positions rep) (rep.ty storeTy)) p ≤ 4 * W := by
    have hq := hnsize p.1 h.1
    have hs' := hpre p.2 h.2
    exact (sizes.prod_le _ _ p).trans (by omega)
  have hall := seq_bound_of_width mono control queryCost routing
    (.first (rep.ty storeTy) (.atomic ports.request))
    (dispatchWithSigning rep bd ports data cost primitive uniform sampler signer)
    sourcePre sourcePre final (4 * W) _ _ hsrc hnat he hd
  apply Bounds.time_mono control queryCost hall
  have hfee := mono (show 32 * W ≤ 128 * W by omega)
  simp only [← Nat.mul_assoc, Nat.reduceMul]
  dsimp only [handlerTime, fee, W] at hfee ⊢
  omega

theorem code_bound_of_components
    (width tapeWidth mc lc sc rc nextSavedCap arityCap portWidth requestTime tagTime randomTime hashTime signingTime : Nat)
    (hh : header ≤ width) (ht : header ≤ tapeWidth) (hs : sc ≤ nextSavedCap)
    (hw : (6 * (nextSavedCap + rc) + 3) * tapeWidth ≤ width)
    (hNat : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ tapeWidth)
    (caps : PortCaps rep bd ports width tapeWidth arityCap portWidth requestTime tagTime)
    (hrandom : Bounds control queryCost (NativeComponents.random rep data cost primitive uniform)
      (fun p => p.1 ≤ arityCap ∧ StoreBound (Q := Q) rep width tapeWidth mc lc sc rc p.2)
      (InputBound (Q := Q) rep .nat tapeWidth width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc) randomTime)
    (hhash : Bounds control queryCost (NativeComponents.hash rep data cost primitive sampler)
      (InputBound (Q := Q) rep hashKey (3 * width) width tapeWidth mc lc sc rc)
      (InputBound (Q := Q) rep scalar (3 * width) width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc) hashTime)
    (hsigning : Bounds control queryCost (NativeComponents.signing rep data cost primitive uniform privatePorts sampler)
      (InputBound (Q := Q) rep message width width tapeWidth mc lc sc rc)
      (InputBound (Q := Q) rep signatureTy (3 * width) width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc) signingTime) :
    Bounds control queryCost (code rep bd ports data cost primitive uniform privatePorts sampler)
      (fun p => RequestBound (Q := Q) rep width arityCap p.1 ∧ StoreBound (Q := Q) rep width tapeWidth mc lc sc rc p.2)
      (fun p => Q.size bd.idx p.1 ≤ portWidth ∧ StoreBound (Q := Q) rep width tapeWidth (mc + 1) (lc + 1) nextSavedCap rc p.2)
      (handlerTime overhead (frameWidth width mc lc portWidth) randomTime hashTime signingTime requestTime tagTime) :=
  codeWithSigning_bound_of_components rep bd ports data cost primitive uniform sampler
    sizes lists laws mono control queryCost routing dispatchLaws
    (NativeComponents.signing rep data cost primitive uniform privatePorts sampler)
    width tapeWidth mc lc sc rc nextSavedCap arityCap portWidth requestTime tagTime randomTime hashTime signingTime
    hh ht hs hw hNat caps hrandom hhash hsigning

end Signatures.Runtime.Schnorr.ListROM.NativeHandler
