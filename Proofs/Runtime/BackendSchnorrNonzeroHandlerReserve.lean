import Proofs.Runtime.BackendSchnorrNonzeroHandlerBudget
import Proofs.Runtime.BackendSchnorrROMHandlerReserve

/-! Capacity reservations for every adaptive nonzero-nonce request. The exact
executed dispatcher consumes one cache reservation and 2*qField+qNonzero+1 tape
reservations. Runtime is charged at the common maximum capacities. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeHandler

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

theorem code_bound_reserved
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
    (portWidth encodeTime tagTime remaining : Nat)
    (caps : PortCaps rep bd ports width tapeWidth arityCap portWidth encodeTime tagTime) :
    Bounds control queryCost (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler)
      (fun p => RequestBound (Q := Q) rep width arityCap p.1 ∧
        ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap
          (2 * fieldQueries + nonzeroQueries + 1) (remaining + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ portWidth ∧
        ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap
          (2 * fieldQueries + nonzeroQueries + 1) remaining p.2)
      (timeBudget overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap tickTime
        comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
        width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime) := by
  apply bound_reserved_of_bounds rep bd control queryCost
    (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler)
    width tapeWidth managedCap liveCap savedCap remainingCap (2 * fieldQueries + nonzeroQueries + 1) arityCap portWidth remaining
    (fun mc lc sc => timeBudget overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth sc remainingCap tickTime
      comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
      width mc lc messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime)
  intro mc _ lc _ sc hsc
  have hsamplerWidth : NativePrivate.samplerWidth sourceWidth tapeWidth (sc + 2 * fieldQueries) remainingCap nonzeroQueries ≤
      NativePrivate.samplerWidth sourceWidth tapeWidth (savedCap + 2 * fieldQueries) remainingCap nonzeroQueries := by
    unfold NativePrivate.samplerWidth NativePrivate.frameWidth
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    omega
  have htick : ∀ n ≤ counter, ∀ size ≤ 6 * NativePrivate.samplerWidth sourceWidth tapeWidth
      (sc + 2 * fieldQueries) remainingCap nonzeroQueries, control.loop n size ≤ tickTime :=
    fun n hn size hs => tick n hn size (hs.trans (Nat.mul_le_mul_left 6 hsamplerWidth))
  have hwidth : (6 * (sc + 2 * fieldQueries + nonzeroQueries + 1 + remainingCap) + 3) * tapeWidth ≤ width :=
    (Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth
  simpa only [Nat.add_assoc] using
    code_bound rep bd ports data cost primitive uniform privatePorts sizes lists laws mono control queryCost
      routing dispatchLaws dataLaws primitiveBound fieldSampler nonzeroSampler fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth sc remainingCap
      counter arityCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
      width mc lc messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime fieldProfile nonzeroProfile htick hh hu hb hz hn hcompare hzero hnatAdd
      hp hr hrequest hresponse hquery hread hreply hsourceTapeWidth hwidth hm hg hscale hsub hgroupZero hgroupZeroTime hscalarAdd portWidth encodeTime tagTime caps

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler
