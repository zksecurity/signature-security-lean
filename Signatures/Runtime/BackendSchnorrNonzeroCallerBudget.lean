import Signatures.Runtime.BackendSchnorrNonzeroHandlerReserve
import Signatures.Runtime.BackendSchnorrROMCallerBudget
import Signatures.Runtime.BackendCallerIndexedResource

/-! Additive caller overhead for the executed nonzero-nonce Schnorr dispatcher.
The attacker supplies its own realized work/query budget; primitive contracts derive
the full handler cost. Capacity reservations cover every adaptive continuation.
Recovery of caller invariants from RunsWithin is a separate boundary theorem. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler

open BackendProgram RawTape ListROM ListROM.NativeInterface ListROM.NativeComponents ListROM.NativeHandler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ K M Input Output : Type} [Field F] [SampleableType F] [SampleableType Fˣ]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output) (ports : Ports (Q := Q) rep bd)
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (fieldLaw : fieldSampler.denote () = ($ᵗ F : ProbComp F))
  (nonzeroLaw : nonzeroSampler.denote () = (fun a : Fˣ => (a : F)) <$> ($ᵗ Fˣ))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

include fieldLaw nonzeroLaw in
omit [C.HasOption] QO OC in
theorem executed_mem_code (q : NativeInterface.Request G₁ M) (saved : Shared.Store F G₁ M)
    (z : Run ((sourceSpec F G₁ M).Range q) × (Shared.Store F G₁ M))
    (hz : z ∈ support ((executed rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler control queryCost q).run saved)) :
    (⟨(⟨q, z.1.value⟩, z.2), z.1.steps⟩ : Run (NativeInterface.Response F G₁ M × (Shared.Store F G₁ M))) ∈
      support ((code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler).run control queryCost (q, saved)) := by
  rw [code_executed_run rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw control queryCost q saved]
  dsimp only [NativeInterface.Response, sourceSpec, OracleSpec.toPFunctor, PFunctor.Idx]
  rw [support_map]
  exact ⟨z, hz, rfl⟩

variable {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

include fieldLaw nonzeroLaw sizes lists laws mono routing dispatchLaws

/-- Internal composition rule. The primitive-derived endpoint below discharges
its per-request budget premise for the actual executed dispatcher. -/
theorem caller_bound_of_handler
    (width tapeWidth managedCap liveCap savedCap remainingCap drawCap arityCap portWidth routeWidth
      fuel localTime tickTime price : Nat)
    (fieldQueries : Fin 3 → Nat) (hh : header ≤ width) (ht : header ≤ tapeWidth)
    (hstoreWidth : (6 * (savedCap + remainingCap) + 3) * tapeWidth ≤ width)
    (hroute : ListROM.NativeHandler.frameWidth width managedCap liveCap portWidth ≤ routeWidth)
    (hhandler : ∀ n, Bounds control queryCost (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler)
      (fun p => RequestBound (Q := Q) rep width arityCap p.1 ∧
        ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap (n + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ portWidth ∧
        ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap n p.2) price)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ q next,
      R.machine.view state = .inr ⟨q, next⟩ →
        RequestBound (Q := Q) rep width arityCap q ∧ ∀ answer, callerInv n (next answer))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (input : Input) (saved : Shared.Store F G₁ M)
    (hiCaller : callerInv fuel (R.machine.init input))
    (hiStore : ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (hbudget : GeneralCaller.Budget R (ListROM.NativeHandler.replies F G₁ M) ListROM.NativeHandler.kind fuel input localTime fieldQueries)
    (z : Run (Option Output × Shared.Store F G₁ M))
    (hz : z ∈ support ((caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel).run control queryCost (input, saved))) :
    ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap 0 z.value.2 ∧
      z.steps ≤ ListROM.NativeHandler.callerTime overhead routeWidth fuel localTime fieldQueries price tickTime := by
  let H := executed rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler control queryCost
  let inv := fun n (p : R.machine.State × Shared.Store F G₁ M) =>
    n ≤ fuel ∧ callerInv n p.1 ∧ ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap n p.2
  let post := ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap 0
  have hw := frame_widths width managedCap liveCap portWidth
  have hstep : ∀ n state saved, inv (n + 1) (state, saved) → ∀ q next,
      R.machine.view state = .inr ⟨q, next⟩ → ∀ p ∈ support ((H q).run saved),
        inv n (next p.1.value, p.2) ∧ (ListROM.NativeHandler.replies F G₁ M).allows q p.1.value ∧ p.1.steps ≤ price := by
    intro n state saved hi q next hv p hp
    obtain ⟨hq, hnext⟩ := hcallerStep n state hi.2.1 q next hv
    have hmem := executed_mem_code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw control queryCost q saved p hp
    have h := hhandler n (q, saved) ⟨hq, hi.2.2⟩ _ hmem
    exact ⟨⟨by have := hi.1; omega, hnext p.1.value, h.1.2⟩, trivial, h.2⟩
  have hpost : ∀ n state saved, inv n (state, saved) → post saved :=
    fun n _ saved hi => reserved_weaken rep width tapeWidth managedCap liveCap savedCap remainingCap drawCap
      0 n (Nat.zero_le n) saved hi.2.2
  have hwidth : ∀ n state saved, inv n (state, saved) →
      Q.size R.state state ≤ routeWidth ∧ Q.size (rep.ty storeTy) saved ≤ routeWidth ∧
      Q.size bd.head (R.machine.head state) ≤ routeWidth := by
    intro n state saved hi
    obtain ⟨hs, hh'⟩ := hcallerWidth n state hi.2.1
    have hstore := store_size rep sizes lists width tapeWidth managedCap liveCap savedCap remainingCap portWidth
      hh ht hstoreWidth saved
      (store_mono rep width tapeWidth managedCap liveCap savedCap remainingCap
        (managedCap + 1) (liveCap + 1) savedCap remainingCap (by omega) (by omega) le_rfl le_rfl saved hi.2.2.store)
    exact ⟨hs, hstore.trans hroute, hh'⟩
  have hreply : ∀ n state saved, inv (n + 1) (state, saved) → ∀ q next,
      R.machine.view state = .inr ⟨q, next⟩ → ∀ p ∈ support ((H q).run saved),
        Q.size bd.idx ⟨q, p.1.value⟩ ≤ routeWidth := by
    intro n state saved hi q next hv p hp
    have hq := (hcallerStep n state hi.2.1 q next hv).1
    have hmem := executed_mem_code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw control queryCost q saved p hp
    exact (hhandler n (q, saved) ⟨hq, hi.2.2⟩ _ hmem).1.1.trans (hw.2.1.trans hroute)
  have hloop : ∀ n state saved, inv n (state, saved) →
      control.loop n (Q.size (Caller.frame R (rep.ty storeTy)) (state, saved)) ≤ tickTime := by
    intro n state saved hi
    obtain ⟨hs, hstore, _⟩ := hwidth n state saved hi
    have hp := sizes.prod_le R.state (rep.ty storeTy) (state, saved)
    dsimp only at hp
    have hhroute : header ≤ routeWidth := by omega
    have hencoded : Q.size (Caller.frame R (rep.ty storeTy)) (state, saved) ≤ 3 * routeWidth := hp.trans (by omega)
    exact htick n hi.1 _ hencoded
  exact Caller.assembled_bound_indexed_of_width R (rep.ty storeTy) control queryCost
    (code rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler) H
    (code_executed_run rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw control queryCost)
    (ListROM.NativeHandler.replies F G₁ M) ListROM.NativeHandler.kind (fun _ => price) inv post tickTime hstep hpost hloop
    sizes laws dispatchLaws mono routing routeWidth fuel localTime fieldQueries (by omega)
    hwidth hreply (input, saved) ⟨le_rfl, hiCaller, hiStore⟩ hiInput hbudget z hz

theorem caller_bound
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
    (portWidth encodeTime tagTime routeWidth fuel callerLocalTime callerTickTime : Nat)
    (caps : PortCaps rep bd ports width tapeWidth arityCap portWidth encodeTime tagTime)
    (hroute : ListROM.NativeHandler.frameWidth width managedCap liveCap portWidth ≤ routeWidth)
    (callerQueries : Fin 3 → Nat) (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ q next,
      R.machine.view state = .inr ⟨q, next⟩ →
        RequestBound (Q := Q) rep width arityCap q ∧ ∀ answer, callerInv n (next answer))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (input : Input) (saved : Shared.Store F G₁ M)
    (hiCaller : callerInv fuel (R.machine.init input))
    (hiStore : ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap
      (2 * fieldQueries + nonzeroQueries + 1) fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (hbudget : GeneralCaller.Budget R (ListROM.NativeHandler.replies F G₁ M) ListROM.NativeHandler.kind fuel input callerLocalTime callerQueries)
    (z : Run (Option Output × Shared.Store F G₁ M))
    (hrunCode : z ∈ support ((caller rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler R fuel).run
      control queryCost (input, saved))) :
    ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap (2 * fieldQueries + nonzeroQueries + 1) 0 z.value.2 ∧
      z.steps ≤ ListROM.NativeHandler.callerTime overhead routeWidth fuel callerLocalTime callerQueries
        (timeBudget overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap tickTime
          comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
          width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime) callerTickTime := by
  have htw : tapeWidth ≤ width := by
    nlinarith only [hstoreWidth, Nat.zero_le ((savedCap + 2 * fieldQueries + nonzeroQueries + 1 + remainingCap) * tapeWidth)]
  exact caller_bound_of_handler rep bd ports data cost primitive uniform privatePorts fieldSampler nonzeroSampler fieldLaw nonzeroLaw control queryCost
    sizes lists laws mono routing dispatchLaws R width tapeWidth managedCap liveCap savedCap remainingCap
    (2 * fieldQueries + nonzeroQueries + 1) arityCap portWidth routeWidth fuel callerLocalTime callerTickTime _ callerQueries
    (hh.trans htw) hh ((Nat.mul_le_mul_right tapeWidth (by omega)).trans hstoreWidth) hroute
    (fun n => code_bound_reserved rep bd ports data cost primitive uniform privatePorts sizes lists laws mono control
      queryCost routing dispatchLaws dataLaws primitiveBound fieldSampler nonzeroSampler fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap
      remainingCap counter arityCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime
      replyTime width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime fieldProfile nonzeroProfile tick hh hu hb hz hn hcompare hzero
      hnatAdd hp hr hrequest hresponse hquery hread hreply hsourceTapeWidth hstoreWidth hm hg hscale hsub hgroupZero hgroupZeroTime hscalarAdd
      portWidth encodeTime tagTime n caps)
    callerInv hcallerStep hcallerWidth hcallerTick input saved hiCaller hiStore hiInput hbudget z hrunCode

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler
