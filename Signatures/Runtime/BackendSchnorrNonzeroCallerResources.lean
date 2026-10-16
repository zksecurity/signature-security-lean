import Signatures.Runtime.BackendSchnorrNonzeroCallerBudget
import Signatures.Runtime.BackendSchnorrROMCallerResources

/-! Whole-caller runtime from measured arbitrary executions and representation
laws. Reachability covers every adaptive continuation; the native handler budget
is derived from both original sampler profiles and primitive/interface contracts. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeHandler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type} [DecidableEq G₁] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  {header : Nat} (sizes : SizeLaws Q header)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (recovery : RequestRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include sizes hrun

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  [Field F] [SampleableType F] [SampleableType Fˣ] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₂] [DecidableEq K]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (ports : Ports (Q := Q) rep bd) (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
  (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include recovery fieldLaw nonzeroLaw lists laws mono routing dispatchLaws

theorem caller_bound_of_resources
    (dataLaws : DataCostLaws rep.data data overhead)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
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
    (portWidth encodeTime tagTime routeWidth fuel callerTickTime : Nat)
    (caps : PortCaps rep bd ports width tapeWidth arityCap portWidth encodeTime tagTime)
    (hroute : ListROM.NativeHandler.frameWidth width managedCap liveCap portWidth ≤ routeWidth)
    (hrequestSize : recovery.recover bound.peakHeadSize ≤ width)
    (harity : recovery.natural.capacity (recovery.recover bound.peakHeadSize) ≤ arityCap)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (input : Input) (saved : Shared.Store F G₁ M)
    (hiStore : ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap
      (2 * fieldQueries + nonzeroQueries + 1) fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (z : Run (Option Output × Shared.Store F G₁ M))
    (hrunCode : z ∈ support ((caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel).run
      control queryCost (input, saved))) :
    ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap (2 * fieldQueries + nonzeroQueries + 1) 0 z.value.2 ∧
      z.steps ≤ ListROM.NativeHandler.callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2) (fun _ => bound.queries)
        (timeBudget overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap tickTime
          comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
          width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime) callerTickTime := by
  exact caller_bound rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw control queryCost
    sizes lists laws mono routing dispatchLaws R dataLaws primitiveBound fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth
    savedCap remainingCap counter arityCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime
    arityTime replyTime width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime fieldProfile nonzeroProfile tick hh hu hb hz hn
    hcompare hzero hnatAdd hp hr hrequest hresponse hquery hread hreply hsourceTapeWidth hstoreWidth hm hg hscale hsub hgroupZero hgroupZeroTime hscalarAdd
    portWidth encodeTime tagTime routeWidth fuel (bound.work + 2 * bound.queries + 2) callerTickTime caps hroute
    (fun _ => bound.queries) (fun _ => GeneralCaller.Reachable R)
    (fun _ state hs q next hv => resource_step rep bd sizes R recovery bound hrun width arityCap
      hrequestSize harity state hs q next hv)
    (fun _ state hs =>
      let widths := GeneralCaller.reachable_sizes R bound hrun state hs
      ⟨widths.1.trans hstate, widths.2.trans hhead⟩)
    hcallerTick input saved (GeneralCaller.reachable_init R input) hiStore hiInput
    (GeneralCaller.budget_of_resources R bound hrun (ListROM.NativeHandler.replies F G₁ M) ListROM.NativeHandler.kind fuel input) z hrunCode

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler
