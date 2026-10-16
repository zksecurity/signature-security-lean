import Signatures.Runtime.BackendSchnorrNonzeroHandler
import Signatures.Runtime.BackendSchnorrNonzeroComponentsBudget
import Signatures.Runtime.BackendSchnorrROMHandlerRoutingBudget

/-! Complete executed nonzero-nonce dispatcher cost from both original sampler
profiles and primitive/interface contracts. Each request reserves at most one
entry in each cache and 2*qField + qNonzero + 1 tape cells. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeHandler

def timeBudget (overhead : Nat → Nat)
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth
      savedCap remainingCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime
      arityTime replyTime width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime
      scalarAddTime portWidth encodeTime tagTime : Nat) : Nat :=
  let hashTime := NativeDraw.challengeTime overhead tapeWidth savedCap remainingCap comparisonTime zeroTime
    (ExecutionProfile.runtimeBound overhead tapeWidth fieldWork fieldVisits fieldQueries tickTime queryTime)
  let adapterTime := 2061 * overhead (8192 * ListROM.NativeComponents.frameWidth width managedCap liveCap)
  handlerTime overhead (ListROM.NativeHandler.frameWidth width managedCap liveCap portWidth)
    (NativeUniform.runtimeBound overhead tapeWidth savedCap remainingCap comparisonTime zeroTime natAddTime
      requestTime responseTime queryTime + adapterTime)
    (NativeCache.managedTime overhead (3 * width) managedCap liveCap messageTime pointTime hashTime + zeroTime + adapterTime)
    (NativeComponents.signingTime overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries
      sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime natAddTime
      requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime
      scaleTime subTime groupZeroTime scalarAddTime)
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
    (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap counter arityCap tickTime
      comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
      width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime : Nat)
    (fieldProfile : ExecutionProfile.Within fieldSampler () fieldWork fieldVisits fieldQueries sourceWidth counter (fun n => n ≤ arityCap))
    (nonzeroProfile : ExecutionProfile.Within nonzeroSampler () nonzeroWork nonzeroVisits nonzeroQueries
      sourceWidth counter (fun n => n ≤ arityCap))
    (tick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth
      (savedCap + 2 * fieldQueries) remainingCap nonzeroQueries, control.loop n size ≤ tickTime)
    (hh : header ≤ tapeWidth) (hu : Q.size rep.data.unit () ≤ tapeWidth)
    (hb : ∀ b, Q.size rep.data.bool b ≤ tapeWidth) (hz : Q.size (rep.ty scalar) (0 : F) ≤ tapeWidth)
    (hn : ∀ n ≤ arityCap + 2, Q.size rep.data.nat n ≤ tapeWidth)
    (hcompare : ∀ a b, Q.size rep.data.nat a ≤ tapeWidth → Q.size rep.data.nat b ≤ tapeWidth →
      (primitiveBound .natEq).time (a, b) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hnatAdd : ∀ n ≤ arityCap, (primitiveBound .natAdd).time (n, 2) ≤ natAddTime)
    (hp : ∀ n ≤ arityCap, Q.size iface.position n ≤ tapeWidth)
    (hr : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.size iface.response ⟨n, r⟩ ≤ tapeWidth)
    (hrequest : ∀ n ≤ arityCap, Q.cost uniform.request n ≤ requestTime)
    (hresponse : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), Q.cost uniform.response ⟨n, r⟩ ≤ responseTime)
    (hquery : ∀ n ≤ arityCap, ∀ r : Fin (n + 1), queryCost n r +
      control.query (Q.size iface.position n) (Q.size iface.response ⟨n, r⟩) ≤ queryTime)
    (hread : ∀ n ≤ arityCap, Q.cost privatePorts.arity n ≤ arityTime)
    (hreply : ∀ n ≤ arityCap, ∀ r, Q.size rep.data.nat r ≤ tapeWidth → Q.cost privatePorts.reply (r, n) ≤ replyTime)
    (hsourceTapeWidth : sourceWidth ≤ tapeWidth)
    (hstoreWidth : (6 * (savedCap + 2 * fieldQueries + nonzeroQueries + 1 + remainingCap) + 3) * tapeWidth ≤ width)
    (hm : ∀ x y : M, Q.size (rep.ty message) x ≤ 3 * width → Q.size (rep.ty message) y ≤ 3 * width →
      (primitiveBound .messageEq).time (x, y) ≤ messageTime)
    (hg : ∀ x y : G₁, Q.size (rep.ty point₁) x ≤ 3 * width → Q.size (rep.ty point₁) y ≤ 3 * width →
      (primitiveBound .point₁Eq).time (x, y) ≤ pointTime)
    (hscale : ∀ z : F, ∀ g : G₁, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty point₁) g ≤ width →
      Q.size (rep.ty point₁) (z • g) ≤ width ∧ (primitiveBound .scale₁).time (z, g) ≤ scaleTime)
    (hsub : ∀ g pk : G₁, Q.size (rep.ty point₁) g ≤ width → Q.size (rep.ty point₁) pk ≤ width →
      Q.size (rep.ty point₁) (g - pk) ≤ width ∧ (primitiveBound .sub₁).time (g, pk) ≤ subTime)
    (hgroupZero : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hgroupZeroTime : (primitiveBound .zero₁).time () ≤ groupZeroTime)
    (hscalarAdd : ∀ z a : F, Q.size (rep.ty scalar) z ≤ width → Q.size (rep.ty scalar) a ≤ width →
      Q.size (rep.ty scalar) (z + a) ≤ width ∧ (primitiveBound .add).time (z, a) ≤ scalarAddTime)
    (portWidth encodeTime tagTime : Nat)
    (caps : PortCaps rep bd ports width tapeWidth arityCap portWidth encodeTime tagTime) :
    Bounds control queryCost (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler)
      (fun p => RequestBound (Q := Q) rep width arityCap p.1 ∧
        StoreBound (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap p.2)
      (fun p => Q.size bd.idx p.1 ≤ portWidth ∧
        StoreBound (Q := Q) rep width tapeWidth (managedCap + 1) (liveCap + 1)
          (savedCap + 2 * fieldQueries + nonzeroQueries + 1) remainingCap p.2)
      (timeBudget overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap tickTime
        comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
        width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime) := by
  have fieldTick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth
      (savedCap + fieldQueries) remainingCap fieldQueries, control.loop n size ≤ tickTime := by
    intro n hn size hs
    apply tick n hn size
    apply hs.trans
    apply Nat.mul_le_mul_left
    unfold NativePrivate.samplerWidth NativePrivate.frameWidth
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    omega
  have fieldWidth : (6 * (savedCap + 2 * fieldQueries + 1 + remainingCap) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth
  obtain ⟨_, hhash, _⟩ := ListROM.NativeComponents.cache_components_bound rep data cost primitive uniform privatePorts
    sizes lists laws mono control queryCost routing dataLaws primitiveBound dispatchLaws.distribute fieldSampler
    fieldWork fieldVisits fieldQueries sourceWidth tapeWidth savedCap remainingCap counter arityCap tickTime
    comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
    width managedCap liveCap messageTime pointTime scaleTime subTime
    fieldProfile fieldTick hh hu hb hz hn hcompare hzero hnatAdd hp hr hrequest hresponse hquery hread hreply
    hsourceTapeWidth fieldWidth hm hg hscale hsub
  have hsign := NativeComponents.signing_bound rep data cost primitive uniform privatePorts sizes lists laws mono
    control queryCost routing dataLaws primitiveBound dispatchLaws.distribute fieldSampler nonzeroSampler
    fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap
    counter arityCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
    width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime
    fieldProfile nonzeroProfile tick hh hu hb hz hn hcompare hzero hnatAdd hp hr hrequest hresponse hquery hread hreply
    hsourceTapeWidth ((Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth)
    hm hg hscale hsub hgroupZero hgroupZeroTime hscalarAdd
  have htw : tapeWidth ≤ width := by
    nlinarith only [hstoreWidth, Nat.zero_le ((savedCap + 2 * fieldQueries + nonzeroQueries + 1 + remainingCap) * tapeWidth)]
  have hrandom := ListROM.NativeComponents.random_bound rep data cost primitive uniform sizes lists laws mono
    control queryCost routing dataLaws primitiveBound width managedCap liveCap tapeWidth savedCap remainingCap
    arityCap comparisonTime zeroTime natAddTime requestTime responseTime queryTime
    hh hu hb hz hn hcompare hzero hnatAdd hp hr hrequest hresponse hquery
    ((Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth)
  unfold timeBudget
  apply codeWithSigning_bound_of_components rep bd ports data cost primitive uniform fieldSampler
    sizes lists laws mono control queryCost routing dispatchLaws
    (NativeComponents.signing rep data cost primitive uniform privatePorts fieldSampler nonzeroSampler)
    width tapeWidth managedCap liveCap savedCap remainingCap
    (savedCap + 2 * fieldQueries + nonzeroQueries + 1) arityCap portWidth encodeTime tagTime _ _ _
    (hh.trans htw) hh (by omega) hstoreWidth (fun n hn' => hn n (by omega)) caps
  · apply Bounds.consequence control queryCost hrandom (fun _ h => h)
    intro output ho
    exact ⟨ho.1, store_mono rep width tapeWidth managedCap liveCap (savedCap + 1) remainingCap
      (managedCap + 1) (liveCap + 1) (savedCap + 2 * fieldQueries + nonzeroQueries + 1) remainingCap
      (by omega) (by omega) (by omega) le_rfl output.2 ho.2⟩
  · apply Bounds.consequence control queryCost hhash (fun _ h => h)
    intro output ho
    exact ⟨ho.1, store_mono rep width tapeWidth (managedCap + 1) (liveCap + 1) (savedCap + 1) remainingCap
      (managedCap + 1) (liveCap + 1) (savedCap + 2 * fieldQueries + nonzeroQueries + 1) remainingCap
      le_rfl le_rfl (by omega) le_rfl output.2 ho.2⟩
  · apply Bounds.consequence control queryCost hsign (fun _ h => h)
    intro output ho
    exact ⟨ho.1, store_mono rep width tapeWidth (managedCap + 1) liveCap
      (savedCap + 2 * fieldQueries + nonzeroQueries) remainingCap
      (managedCap + 1) (liveCap + 1) (savedCap + 2 * fieldQueries + nonzeroQueries + 1) remainingCap
      le_rfl (by omega) (by omega) le_rfl output.2 ho.2⟩

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler
