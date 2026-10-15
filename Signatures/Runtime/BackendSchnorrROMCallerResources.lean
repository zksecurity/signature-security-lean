import Signatures.Runtime.BackendSchnorrROMCallerBudget
import Signatures.Runtime.BackendSchnorrROMRequestRecovery

/-! Whole-caller runtime from measured arbitrary executions and representation
laws. Reachability covers every adaptive continuation; the native handler budget
is derived from original sampler profiles and primitive/interface contracts. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

open BackendProgram RawTape NativeInterface NativeComponents

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

include recovery in
theorem reachable_request (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (q : NativeInterface.Request G₁ M) (next : (sourceSpec F G₁ M).Range q → R.machine.State)
    (hv : R.machine.view state = .inr ⟨q, next⟩) :
    let width := recovery.recover bound.peakHeadSize
    RequestBound (Q := Q) rep width (recovery.natural.capacity width) q := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inr_of_view hv] at hh
  have hp := (sizes.sum_payload_le bd.out bd.pos (.inr q)).trans hh
  have hm := recovery.monotone hp
  exact requestBound_mono rep _ _ _ _ hm (recovery.natural.monotone hm) q (recovery.request q)

theorem reachable_output (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (out : Output) (hv : R.machine.view state = .inl out) :
    Q.size bd.out out ≤ bound.peakHeadSize := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inl_of_view hv] at hh
  exact (sizes.sum_payload_le bd.out bd.pos (.inl out)).trans hh

include recovery in
theorem resource_step (width arity : Nat)
    (hw : recovery.recover bound.peakHeadSize ≤ width)
    (ha : recovery.natural.capacity (recovery.recover bound.peakHeadSize) ≤ arity)
    (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (q : NativeInterface.Request G₁ M) (next : (sourceSpec F G₁ M).Range q → R.machine.State)
    (hv : R.machine.view state = .inr ⟨q, next⟩) :
    RequestBound (Q := Q) rep width arity q ∧ ∀ answer, GeneralCaller.Reachable R (next answer) :=
  ⟨requestBound_mono rep _ _ width arity hw ha q
    (reachable_request rep bd sizes R recovery bound hrun state hs q next hv),
    fun answer => GeneralCaller.reachable_step R state hs q next hv answer⟩

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₂] [DecidableEq K]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (ports : Ports (Q := Q) rep bd) (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (privatePorts : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sample : sampler.denote () = ($ᵗ F : ProbComp F))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include recovery sample lists laws mono routing dispatchLaws

theorem caller_bound_of_resources
    (dataLaws : DataCostLaws rep.data data overhead)
    (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
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
    (portWidth encodeTime tagTime routeWidth fuel callerTickTime : Nat)
    (caps : PortCaps rep bd ports width tapeWidth arityCap portWidth encodeTime tagTime)
    (hroute : frameWidth width managedCap liveCap portWidth ≤ routeWidth)
    (hrequestSize : recovery.recover bound.peakHeadSize ≤ width)
    (harity : recovery.natural.capacity (recovery.recover bound.peakHeadSize) ≤ arityCap)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hcallerTick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ callerTickTime)
    (input : Input) (saved : Shared.Store F G₁ M)
    (hiStore : ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap
      (2 * queries + 1) fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (z : Run (Option Output × Shared.Store F G₁ M))
    (hrunCode : z ∈ support ((caller rep bd ports data cost primitive uniform privatePorts sampler R fuel).run
      control queryCost (input, saved))) :
    ReservedState (Q := Q) rep width tapeWidth managedCap liveCap savedCap remainingCap (2 * queries + 1) 0 z.value.2 ∧
      z.steps ≤ callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2) (fun _ => bound.queries)
        (timeBudget overhead work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime
          comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime
          width managedCap liveCap messageTime pointTime scaleTime subTime portWidth encodeTime tagTime) callerTickTime := by
  exact caller_bound rep bd ports data cost primitive uniform privatePorts sampler sample control queryCost
    sizes lists laws mono routing dispatchLaws R dataLaws primitiveBound work visits queries sourceWidth tapeWidth
    savedCap remainingCap counter arityCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime
    arityTime replyTime width managedCap liveCap messageTime pointTime scaleTime subTime hsource tick hh hu hb hz hn
    hcompare hzero hadd hp hr hrequest hresponse hquery hread hreply hsourceTapeWidth hstoreWidth hm hg hscale hsub
    portWidth encodeTime tagTime routeWidth fuel (bound.work + 2 * bound.queries + 2) callerTickTime caps hroute
    (fun _ => bound.queries) (fun _ => GeneralCaller.Reachable R)
    (fun _ state hs q next hv => resource_step rep bd sizes R recovery bound hrun width arityCap
      hrequestSize harity state hs q next hv)
    (fun _ state hs =>
      let widths := GeneralCaller.reachable_sizes R bound hrun state hs
      ⟨widths.1.trans hstate, widths.2.trans hhead⟩)
    hcallerTick input saved (GeneralCaller.reachable_init R input) hiStore hiInput
    (GeneralCaller.budget_of_resources R bound hrun (replies F G₁ M) kind fuel input) z hrunCode

end Signatures.Runtime.Schnorr.ListROM.NativeHandler
