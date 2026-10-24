import Proofs.Runtime.BackendSchnorrROMHandlerRoutingBudget

/-! Complete executed ordinary-ROM dispatcher budget from original sampler
resources and primitive/interface contracts. Each request reserves at most one
entry in each cache and twice the sampler query allowance plus one tape cell. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

open BackendProgram RawTape NativeInterface NativeComponents

def timeBudget (overhead : Nat → Nat)
    (work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime
      scaleTime subTime portWidth encodeTime tagTime : Nat) : Nat :=
  let firstTime := NativePrivate.samplerTime overhead work visits queries sourceWidth tapeWidth
    savedCap remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
  let secondTime := NativePrivate.samplerTime overhead work visits queries sourceWidth tapeWidth
    (savedCap + queries) remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
  let hashTime := NativeDraw.challengeTime overhead tapeWidth savedCap remainingCap comparisonTime zeroTime
    (ExecutionProfile.runtimeBound overhead tapeWidth work visits queries tickTime queryTime)
  let adapterTime := 2061 * overhead (8192 * NativeComponents.frameWidth width managedCap liveCap)
  handlerTime overhead (frameWidth width managedCap liveCap portWidth)
    (NativeUniform.runtimeBound overhead tapeWidth savedCap remainingCap comparisonTime zeroTime addTime
      requestTime responseTime queryTime + adapterTime)
    (NativeCache.managedTime overhead (3 * width) managedCap liveCap messageTime pointTime hashTime + zeroTime + adapterTime)
    (NativeCache.signingTime overhead width managedCap messageTime pointTime scaleTime subTime firstTime secondTime + adapterTime)
    encodeTime tagTime

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive] [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input Output : Type} [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  (ports : NativeInterface.Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include sizes lists laws mono routing dispatchLaws

theorem code_bound
    (dataLaws : DataCostLaws rep.data data overhead)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
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
    (portWidth encodeTime tagTime : Nat)
    (caps : PortCaps rep bd ports width tapeWidth arityCap portWidth encodeTime tagTime) :
    Bounds control queryCost (code rep bd ports data cost primitive uniform privatePorts sampler)
      (fun p => RequestBound (Q := Q) rep width arityCap p.1 ∧
        StoreBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap p.2)
      (fun p => Q.size bd.idx p.1 ≤ portWidth ∧
        StoreBound (Q := Q) rep width tapeWidth (managedCap + 1) (liveCap + 1)
          (savedCap + 2 * queries + 1) remainingCap p.2)
      (timeBudget overhead work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime
        comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
        width managedCap liveCap messageTime pointTime scaleTime subTime portWidth encodeTime tagTime) := by
  obtain ⟨_, hhash, hsign⟩ := NativeComponents.cache_components_bound rep data cost primitive uniform privatePorts
    sizes lists laws mono control queryCost routing dataLaws primitiveBound dispatchLaws.distribute sampler
    work visits queries sourceWidth tapeWidth savedCap remainingCap counter arityCap tickTime
    comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
    width managedCap liveCap messageTime pointTime scaleTime subTime
    hsource tick hh hu hb hz hn hcompare hzero hadd hp hr hrequest hresponse hquery hread hreply
    hsourceTapeWidth hstoreWidth hm hg hscale hsub
  have htw : tapeWidth ≤ width := by
    nlinarith only [hstoreWidth, Nat.zero_le ((savedCap + 2 * queries + 1 + remainingCap) * tapeWidth)]
  have hrandom := NativeComponents.random_bound rep data cost primitive uniform sizes lists laws mono
    control queryCost routing dataLaws primitiveBound width managedCap liveCap tapeWidth savedCap remainingCap
    arityCap comparisonTime zeroTime addTime requestTime responseTime queryTime
    hh hu hb hz hn hcompare hzero hadd hp hr hrequest hresponse hquery
    ((Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth)
  unfold timeBudget
  apply code_bound_of_components rep bd ports data cost primitive uniform privatePorts sampler
    sizes lists laws mono control queryCost routing dispatchLaws width tapeWidth managedCap liveCap savedCap remainingCap
    (savedCap + 2 * queries + 1) arityCap portWidth encodeTime tagTime _ _ _
    (hh.trans htw) hh (by omega) hstoreWidth (fun n hn' => hn n (by omega)) caps
  · apply Bounds.consequence control queryCost hrandom (fun _ h => h)
    intro output ho
    exact ⟨ho.1, store_mono rep width tapeWidth managedCap liveCap (savedCap + 1) remainingCap
      (managedCap + 1) (liveCap + 1) (savedCap + 2 * queries + 1) remainingCap
      (by omega) (by omega) (by omega) le_rfl output.2 ho.2⟩
  · apply Bounds.consequence control queryCost hhash (fun _ h => h)
    intro output ho
    exact ⟨ho.1, store_mono rep width tapeWidth (managedCap + 1) (liveCap + 1) (savedCap + 1) remainingCap
      (managedCap + 1) (liveCap + 1) (savedCap + 2 * queries + 1) remainingCap
      le_rfl le_rfl (by omega) le_rfl output.2 ho.2⟩
  · apply Bounds.consequence control queryCost hsign (fun _ h => h)
    intro output ho
    exact ⟨ho.1, store_mono rep width tapeWidth (managedCap + 1) liveCap (savedCap + 2 * queries) remainingCap
      (managedCap + 1) (liveCap + 1) (savedCap + 2 * queries + 1) remainingCap
      le_rfl (by omega) (by omega) le_rfl output.2 ho.2⟩

end Signatures.Runtime.Schnorr.ListROM.NativeHandler
