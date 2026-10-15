import Signatures.Runtime.BackendSchnorrAGMCallerBudget
import Signatures.Runtime.BackendSchnorrAGMRequestRecovery
import Signatures.Runtime.GeneralCallerResources

/-! Derive Schnorr caller conditions from measured executions and encoding laws.
Reachability covers every adaptive continuation. All request cells and nested
coefficient rows are bounded; numeric random arities need not be polynomial in
their encoded width. The native handler's full cost is derived from primitives. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SchnorrAGM.Native.Handler

open BackendProgram Interface

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ K M Input Output : Type}
  [DecidableEq (SourceRequest F G₁ M)]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (bd : Boundary C (sourceSpec F G₁ M).toPFunctor Input Output)
  {header : Nat} (sizes : SizeLaws Q header)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (recovery : RequestRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include sizes hrun

include recovery in
theorem reachable_request (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (q : SourceRequest F G₁ M) (next : (sourceSpec F G₁ M).Range q → R.machine.State)
    (hv : R.machine.view state = .inr ⟨q, next⟩) :
    let width := recovery.recover bound.peakHeadSize
    RequestBound (Q := Q) rep width width width width (recovery.natural.capacity width) q := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inr_of_view hv] at hh
  have hp := (sizes.sum_payload_le bd.out bd.pos (.inr q)).trans hh
  have hm := recovery.monotone hp
  exact requestBound_mono rep _ _ _ _ _ _ _ _ _ _ hm hm hm hm
    (recovery.natural.monotone hm) q (recovery.request q)

/-- The entire returned encoding is measured, including all explanation rows. -/
theorem reachable_output (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (out : Output) (hv : R.machine.view state = .inl out) :
    Q.size bd.out out ≤ bound.peakHeadSize := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inl_of_view hv] at hh
  exact (sizes.sum_payload_le bd.out bd.pos (.inl out)).trans hh

include recovery in
theorem resource_step (width groups rows coefficients arity : Nat)
    (hw : recovery.recover bound.peakHeadSize ≤ width)
    (hg : recovery.recover bound.peakHeadSize ≤ groups)
    (hr : recovery.recover bound.peakHeadSize ≤ rows)
    (hc : recovery.recover bound.peakHeadSize ≤ coefficients)
    (ha : recovery.natural.capacity (recovery.recover bound.peakHeadSize) ≤ arity)
    (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (q : SourceRequest F G₁ M) (next : (sourceSpec F G₁ M).Range q → R.machine.State)
    (hv : R.machine.view state = .inr ⟨q, next⟩) :
    RequestBound (Q := Q) rep width groups rows coefficients arity q ∧
      ∀ answer, GeneralCaller.Reachable R (next answer) := by
  exact ⟨requestBound_mono rep _ _ _ _ _ width groups rows coefficients arity hw hg hr hc ha q
    (reachable_request rep bd sizes R recovery bound hrun state hs q next hv),
    fun answer => GeneralCaller.reachable_step R state hs q next hv answer⟩

variable [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QD : Q.IsDistributive]
  [QO : Q.HasOption] [OC : OptionCode (Q := Q)]
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : BackendProgram.Interface (C := C) unifSpec}
  (ports : Ports (Q := Q) rep bd) (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (randomPorts : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead) (mono : Monotone overhead)
  (routing : RoutingCostLaws control overhead) (dispatchLaws : DispatchCostLaws (Q := Q) overhead)

include recovery lists laws dataLaws mono routing dispatchLaws

theorem caller_bound_of_resources
    (width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth routeWidth fuel tickTime : Nat)
    (t : Times) (hh : header ≤ width)
    (hroute : frameWidth width cap basisCap signedCap groupCap rowCap coeffCap portWidth ≤ routeWidth)
    (caps : PortCaps rep bd ports width groupCap rowCap coeffCap arityCap portWidth t.requestTime t.tagTime)
    (primitives : PrimitiveCaps rep cost primitive randomPorts sampler control queryCost primitiveBound width basisCap arityCap t)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hgroups : recovery.recover bound.peakHeadSize ≤ groupCap)
    (hrows : recovery.recover bound.peakHeadSize ≤ rowCap)
    (hcoeff : recovery.recover bound.peakHeadSize ≤ coeffCap)
    (harity : recovery.natural.capacity (recovery.recover bound.peakHeadSize) ≤ arityCap)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (input : Input) (saved : (G₁ × G₁) × EncodedState F G₁ M)
    (hiStore : ReservedState (Q := Q) rep width cap basisCap signedCap fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (z : Run (Option Output × ((G₁ × G₁) × EncodedState F G₁ M)))
    (hz : z ∈ support ((caller rep bd ports data cost primitive randomPorts sampler R fuel).run control queryCost (input, saved))) :
    ReservedState (Q := Q) rep width cap basisCap signedCap 0 z.value.2 ∧
      z.steps ≤ callerTime overhead routeWidth fuel (bound.work + 2 * bound.queries + 2)
        (fun _ => bound.queries) (timeBudget overhead width cap basisCap signedCap groupCap rowCap coeffCap portWidth t) tickTime := by
  exact caller_bound rep bd ports data cost primitive randomPorts sampler control queryCost primitiveBound
    sizes lists laws dataLaws mono routing dispatchLaws R
    width cap basisCap signedCap groupCap rowCap coeffCap arityCap portWidth routeWidth fuel
    (bound.work + 2 * bound.queries + 2) tickTime t (fun _ => bound.queries) hh hroute caps primitives
    (fun _ => GeneralCaller.Reachable R)
    (fun _ state hs q next hv => resource_step rep bd sizes R recovery bound hrun
      width groupCap rowCap coeffCap arityCap hrequest hgroups hrows hcoeff harity state hs q next hv)
    (fun _ state hs =>
      let widths := GeneralCaller.reachable_sizes R bound hrun state hs
      ⟨widths.1.trans hstate, widths.2.trans hhead⟩)
    htick input saved (GeneralCaller.reachable_init R input) hiStore hiInput
    (GeneralCaller.budget_of_resources R bound hrun (replies F G₁ M) kind fuel input) z hz

end Signatures.Runtime.SchnorrAGM.Native.Handler
