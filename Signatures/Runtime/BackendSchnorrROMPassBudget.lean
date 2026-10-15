import Signatures.Runtime.BackendSchnorrROMPassSetup
import Signatures.Runtime.BackendSchnorrROMPassTerminalComposition

/-! Complete native pass runtime from measured general-caller resources and
primitive/encoding contracts. Initialization, all attacker queries, final live
hashing, every boundary conversion and both cutoff/completion paths are charged.
No completed caller, sampler, handler, verification or pass budget is assumed. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape NativeInterface NativeComponents

def frameWidth (width managedCap liveCap routeWidth : Nat) : Nat :=
  routeWidth + NativeComponents.frameWidth width managedCap liveCap

/-- Final live lookup before its store/forgery adapters. The original scalar
sampler is charged from its measured execution profile. -/
def finalHashTime (overhead : Nat → Nat)
    (work visits queries tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime queryTime
      width liveCap messageTime pointTime : Nat) : Nat :=
  NativeCache.liveTime overhead (3 * width) liveCap messageTime pointTime
    (NativeDraw.challengeTime overhead tapeWidth savedCap remainingCap comparisonTime zeroTime
      (ExecutionProfile.runtimeBound overhead tapeWidth work visits queries tickTime queryTime)) + zeroTime

def timeBudget (overhead : Nat → Nat) (frame callerTime hashTime inputTime outputTime optionalTime : Nat) : Nat :=
  callerTime + hashTime + inputTime + outputTime + optionalTime + 8192 * overhead (8192 * frame)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [Q.HasOption] [OptionCode (Q := Q)]
  {F G₁ G₂ K M : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor G₁ (M × G₁ × F))
  (boundary : DataPorts (Q := Q) rep bd) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sample : sampler.denote () = ($ᵗ F : ProbComp F))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatch : DispatchCostLaws (Q := Q) overhead)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (recovery : NativeHandler.RequestRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include sample sizes lists laws dataLaws primitiveBound mono routing dispatch hrun

theorem code_bound_of_resources
    (work visits queries sourceWidth tapeWidth savedCap remainingCap counter arityCap tickTime
      comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
      width managedCap liveCap messageTime pointTime scaleTime subTime : Nat)
    (hsource : ExecutionProfile.Within sampler () work visits queries sourceWidth counter (fun n => n ≤ arityCap))
    (tick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth
      (savedCap + queries) remainingCap queries, control.loop n size ≤ tickTime)
    (hh : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ tapeWidth)
    (hb : ∀ b, Q.size rep.data.bool b ≤ tapeWidth) (hz : Q.size (rep.ty scalar) (0 : F) ≤ tapeWidth)
    (hn : ∀ n ≤ arityCap + 2, Q.size rep.data.nat n ≤ tapeWidth)
    (hcompare : ∀ a b, Q.size rep.data.nat a ≤ tapeWidth → Q.size rep.data.nat b ≤ tapeWidth →
      (primitiveBound .natEq).time (a, b) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hadd : ∀ n ≤ arityCap, (primitiveBound .natAdd).time (n, 2) ≤ addTime)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ tapeWidth)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ tapeWidth)
    (hrequest : ∀ n ≤ arityCap, Q.cost uniform.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost uniform.response ⟨n, r⟩ ≤ responseTime)
    (hquery : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ queryTime)
    (hread : ∀ n ≤ arityCap, Q.cost privatePorts.arity n ≤ arityTime)
    (hreply : ∀ n ≤ arityCap, ∀ r, Q.size rep.data.nat r ≤ tapeWidth → Q.cost privatePorts.reply (r, n) ≤ replyTime)
    (hsourceTapeWidth : sourceWidth ≤ tapeWidth)
    (hstoreWidth : (6 * (savedCap + 2 * queries + 1 + remainingCap) + 3) * tapeWidth ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ 3 * width → Q.size (rep.ty point₁) y ≤ 3 * width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (hscale : ∀ z : F, ∀ g : G₁, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty point₁) g ≤ width →
      Q.size (rep.ty point₁) (z • g) ≤ width ∧ (primitiveBound .scale₁).time (z, g) ≤ scaleTime)
    (hsub : ∀ g pk : G₁, Q.size (rep.ty point₁) g ≤ width → Q.size (rep.ty point₁) pk ≤ width →
      Q.size (rep.ty point₁) (g - pk) ≤ width ∧ (primitiveBound .sub₁).time (g, pk) ≤ subTime)
    (portWidth encodeTime tagTime routeWidth fuel callerTickTime initialSavedCap inputTime outputTime optionalTime : Nat)
    (handlerCaps : NativeHandler.PortCaps rep bd ports width tapeWidth arityCap portWidth encodeTime tagTime)
    (boundaryCaps : PortCaps rep bd boundary width routeWidth bound.peakHeadSize inputTime outputTime optionalTime)
    (hroute : NativeHandler.frameWidth width managedCap liveCap portWidth ≤ routeWidth)
    (hrequestSize : recovery.recover bound.peakHeadSize ≤ width)
    (harity : recovery.natural.capacity (recovery.recover bound.peakHeadSize) ≤ arityCap)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (hmanaged : fuel ≤ managedCap) (hlive : fuel ≤ liveCap)
    (hsaved : initialSavedCap + fuel * (2 * queries + 1) ≤ savedCap) :
    Bounds control queryCost (code rep bd boundary data cost primitive sampler ports uniform privatePorts R fuel)
      (fun p => ConfigBound (Q := Q) rep width p.2 ∧
        NativeUniform.StateBound (Q := Q) rep tapeWidth initialSavedCap remainingCap p.1)
      (ResultBound (Q := Q) rep width tapeWidth managedCap (liveCap + 1) (savedCap + 1) remainingCap)
      (timeBudget overhead (frameWidth width managedCap liveCap routeWidth)
        (NativeHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2) (fun _ => bound.queries)
          (NativeHandler.timeBudget overhead work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime
            comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
            width managedCap liveCap messageTime pointTime scaleTime subTime portWidth encodeTime tagTime) callerTickTime)
        (finalHashTime overhead work visits queries tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime
          queryTime width liveCap messageTime pointTime) inputTime outputTime optionalTime) := by
  let W := frameWidth width managedCap liveCap routeWidth
  let inv := NativeHandler.ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap
    (2 * queries + 1) fuel
  let pre := fun p : inputTy.Value (cryptoBase F G₁ G₂ K M) => ConfigBound (Q := Q) rep width p.2 ∧
    NativeUniform.StateBound (Q := Q) rep tapeWidth initialSavedCap remainingCap p.1
  let started := fun p : G₁ × Shared.Store F G₁ M => Q.size bd.input p.1 ≤ routeWidth ∧ inv p.2
  let returned := fun p : Option (M × G₁ × F) × Shared.Store F G₁ M =>
    ResultReady (Q := Q) bd bound.peakHeadSize p.1 ∧
      StoreBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap p.2
  let post := ResultBound (Q := Q) rep width tapeWidth managedCap (liveCap + 1) (savedCap + 1) remainingCap
  have htw : tapeWidth ≤ width := by
    nlinarith only [hstoreWidth, Nat.zero_le ((savedCap + 2 * queries + 1 + remainingCap) * tapeWidth)]
  have hw : (6 * (savedCap + remainingCap) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth
  have hwFinal : (6 * (savedCap + 1 + remainingCap) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth
  have hframe : (12 * (managedCap + liveCap) + 40) * width ≤ W := by
    dsimp only [W, frameWidth, NativeComponents.frameWidth]
    nlinarith only [Nat.zero_le ((managedCap + liveCap) * width)]
  have hW : width ≤ W := by nlinarith only [hframe, Nat.zero_le ((managedCap + liveCap) * width)]
  have hrouteW : routeWidth ≤ W := Nat.le_add_right _ _
  have hnativeW : NativeComponents.frameWidth width managedCap liveCap ≤ W := Nat.le_add_left _ _
  have hstore (saved) (hi : StoreBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap saved) :
      Q.size (rep.ty storeTy) saved ≤ W := by
    have h := store_size rep sizes lists width tapeWidth managedCap liveCap savedCap remainingCap
      (hh.trans htw) hh hw saved hi
    nlinarith only [h, hframe]
  have hiSize (p) (hi : pre p) : Q.size (rep.ty inputTy) p ≤ 4 * W := by
    have hc := config_size rep sizes width (hh.trans htw) p.2 hi.1
    have htape := NativeUniform.state_size rep sizes lists tapeWidth initialSavedCap remainingCap hh p.1 hi.2
    have hw0 : (6 * (initialSavedCap + remainingCap) + 3) * tapeWidth ≤ width :=
      (Nat.mul_le_mul_right tapeWidth (by omega)).trans hw
    have hp' := sizes.prod_le (rep.ty NativeUniform.stateTy) (rep.ty configTy) p
    change Q.size (rep.ty inputTy) p ≤ _ at hp'
    nlinarith only [hc, htape, hw0, hp', hh, htw, hframe, Nat.zero_le ((managedCap + liveCap) * width)]
  have hsSize (p) (hi : started p) : Q.size (StepClass.HasProd.prod bd.input (rep.ty storeTy)) p ≤ 4 * W := by
    have hs' := hstore p.2 hi.2.store
    have hb' := hi.1.trans hrouteW
    have hp' := sizes.prod_le bd.input (rep.ty storeTy) p
    omega
  have hrSize (p) (hi : returned p) : Q.size (Caller.result (bd := bd) (rep.ty storeTy)) p ≤ 4 * W := by
    have hs' := hstore p.2 hi.2
    have ho' : Q.size (StepClass.HasOption.option bd.out) p.1 ≤ 2 * W := by
      cases hopt : p.1 with
      | none => exact (sizes.none_le bd.out).trans (by omega)
      | some out =>
          have ho' := (hi.1 out hopt).trans (hhead.trans hrouteW)
          exact (sizes.some_le bd.out out).trans (by omega)
    have hp' := sizes.prod_le (StepClass.HasOption.option bd.out) (rep.ty storeTy) p
    change Q.size (Caller.result (bd := bd) (rep.ty storeTy)) p ≤ _ at hp'
    omega
  have hsetup := setup_bound (iface := iface) rep bd boundary data cost primitive sizes lists laws dataLaws mono
    control queryCost routing width tapeWidth managedCap liveCap savedCap remainingCap initialSavedCap
    (2 * queries + 1) fuel routeWidth W inputTime (hh.trans htw) hh (hu.trans htw) hw hframe hrouteW
    hmanaged hlive hsaved boundaryCaps.input
  have hcaller : Bounds control queryCost
      (NativeHandler.caller rep bd ports data cost primitive uniform privatePorts sampler R fuel) started returned
      (NativeHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2) (fun _ => bound.queries)
        (NativeHandler.timeBudget overhead work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime
          comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
          width managedCap liveCap messageTime pointTime scaleTime subTime portWidth encodeTime tagTime) callerTickTime) := by
    intro input hi z hz'
    obtain ⟨hout, htime⟩ := NativeHandler.caller_bound_of_resources rep bd sizes R recovery bound hrun
      ports data cost primitive uniform privatePorts sampler sample control queryCost lists laws mono routing dispatch
      dataLaws primitiveBound work visits queries sourceWidth tapeWidth savedCap remainingCap counter arityCap tickTime
      comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
      width managedCap liveCap messageTime pointTime scaleTime subTime
      hsource tick hh hu hb hz hn hcompare hzero hadd hp hr hrequest hresponse hquery hread hreply hsourceTapeWidth
      hstoreWidth hm hg hscale hsub portWidth encodeTime tagTime routeWidth fuel callerTickTime handlerCaps hroute
      hrequestSize harity hstate hhead hcallerTick input.1 input.2 hi.2 hi.1 z hz'
    refine ⟨⟨?_, hout.store⟩, htime⟩
    exact NativeHandler.caller_output_size_of_resources rep bd ports data cost primitive uniform privatePorts sampler
      sample control queryCost R bound hrun sizes fuel input.1 input.2 z hz'
  obtain ⟨hfinal, _, _⟩ := NativeComponents.cache_components_bound rep data cost primitive uniform privatePorts
    sizes lists laws mono control queryCost routing dataLaws primitiveBound dispatch.distribute sampler
    work visits queries sourceWidth tapeWidth savedCap remainingCap counter arityCap tickTime
    comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
    width managedCap liveCap messageTime pointTime scaleTime subTime
    hsource tick hh hu hb hz hn hcompare hzero hadd hp hr hrequest hresponse hquery hread hreply
    hsourceTapeWidth hstoreWidth hm hg hscale hsub
  have hverify := verify_bound_of_finalHash rep data cost primitive sizes lists laws dataLaws mono control queryCost routing
    sampler width tapeWidth managedCap liveCap savedCap remainingCap (savedCap + 1) _
    (hh.trans htw) hh (hu.trans htw) (by omega) hwFinal hfinal
  have hterminal := terminal_bound_of_verification rep bd boundary data cost primitive sizes lists laws dataLaws mono
    control queryCost routing dispatch sampler width tapeWidth managedCap liveCap savedCap remainingCap (savedCap + 1)
    W bound.peakHeadSize outputTime optionalTime _ (hh.trans htw) hh (hu.trans htw) (by omega) hwFinal hframe
    (hhead.trans hrouteW) boundaryCaps.output boundaryCaps.optional hverify
  have htail := seq_bound_of_width mono control queryCost routing _ _ started returned post (4 * W) _ _
    hsSize hrSize hcaller hterminal
  have hall := seq_bound_of_width mono control queryCost routing _ _ pre started post (4 * W) _ _
    hiSize hsSize hsetup htail
  apply Bounds.time_mono control queryCost hall
  have hsmall := mono (show 32 * (4 * W) ≤ 8192 * W by omega)
  have hnative := mono (Nat.mul_le_mul_left 8192 hnativeW)
  dsimp only [timeBudget, finalHashTime]
  change _ ≤ _ + _ + inputTime + outputTime + optionalTime + 8192 * overhead (8192 * W)
  omega

end Signatures.Runtime.Schnorr.ListROM.NativePass
