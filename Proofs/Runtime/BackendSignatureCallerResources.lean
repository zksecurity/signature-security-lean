import Proofs.Runtime.BackendSignatureCallerBudget
import Proofs.Runtime.GeneralCallerResources

/-! Recover native signature-caller conditions from the attacker's own measured
execution resources. Request decoding has an explicit representation-level size
law; native ports separately account for its execution cost. Reachability and
continuation closure are derived, not extra attacker assumptions. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SignatureHandler

open BackendProgram Coron

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {F G₁ G₂ M Input Output : Type} {randomBound : Nat}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input Output)

/-- Size expansion from the caller's request representation to native payloads.
This law does not make decoding free: `PortCaps` still charges its actual code. -/
structure RequestRecovery where
  recover : Nat → Nat
  monotone : Monotone recover
  request : ∀ i, RequestSized (Q := Q) rep (recover (Q.size bd.pos i)) i

variable {header : Nat} (sizes : SizeLaws Q header)

include sizes

/-- Shared request encodings need no size expansion. -/
def RequestRecovery.canonical (hpos : bd.pos = generalPositions rep randomBound) :
    RequestRecovery (Q := Q) rep bd where
  recover := id
  monotone := monotone_id
  request := by
    intro i
    rw [hpos]
    have houter := sizes.sum_payload_le
      (StepClass.HasSum.sum (rep.ty (boundedNat randomBound)) (rep.ty message)) (rep.ty message) i
    rcases i with (n | m) | m
    · have hinner := sizes.sum_payload_le (rep.ty (boundedNat randomBound)) (rep.ty message) (.inl n)
      exact hinner.trans houter
    · have hinner := sizes.sum_payload_le (rep.ty (boundedNat randomBound)) (rep.ty message) (.inr m)
      exact hinner.trans houter
    · exact houter

variable [DecidableEq M]
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))
  (recovery : RequestRecovery (Q := Q) rep bd)
  (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include hrun

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

include recovery in
theorem reachable_request (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (i : GeneralRequest M randomBound) (next : (generalSpec M G₁ randomBound).Range i → R.machine.State)
    (hv : R.machine.view state = .inr ⟨i, next⟩) :
    RequestSized (Q := Q) rep (recovery.recover bound.peakHeadSize) i := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inr_of_view hv] at hh
  have hp := (sizes.sum_payload_le bd.out bd.pos (.inr i)).trans hh
  have hr := recovery.request i
  have hm := recovery.monotone hp
  rcases i with (n | m) | m <;> exact hr.trans hm

/-- The entire returned encoding is bounded, including any representation
coefficients. Projecting a message or recovering list lengths is a separate law. -/
theorem reachable_output (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (out : Output) (hv : R.machine.view state = .inl out) :
    Q.size bd.out out ≤ bound.peakHeadSize := by
  have hh := (GeneralCaller.reachable_sizes R bound hrun state hs).2
  rw [R.machine.head_eq_inl_of_view hv] at hh
  exact (sizes.sum_payload_le bd.out bd.pos (.inl out)).trans hh

include recovery in
theorem resource_step (width : Nat) (hwidth : recovery.recover bound.peakHeadSize ≤ width)
    (state : R.machine.State) (hs : GeneralCaller.Reachable R state)
    (i : GeneralRequest M randomBound) (next : (generalSpec M G₁ randomBound).Range i → R.machine.State)
    (hv : R.machine.view state = .inr ⟨i, next⟩) :
    RequestSized (Q := Q) rep width i ∧ ∀ reply, GeneralCaller.Reachable R (next reply) := by
  have hr := reachable_request rep bd sizes R recovery bound hrun state hs i next hv
  refine ⟨?_, fun reply => GeneralCaller.reachable_step R state hs i next hv reply⟩
  rcases i with (r | m) | m <;> exact hr.trans hwidth

variable [Zero G₁] [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {iface : Interface (C := C) unifSpec} {S : Type}
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (store : C.Str S)
  (reply : (signing : Bool) → Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty message) store) (StepClass.HasProd.prod (rep.ty point₁) store))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)

include recovery localLaws dispatchLaws mono routing

/-- Substitute a measured caller resource bound into native signature dispatch.
The supplied handler budget is discharged by each reduction's primitive-derived
certificate. No custom caller invariant or complete-caller budget is assumed. -/
theorem caller_bound_of_resources (storeInv : Nat → S → Prop) (post : S → Prop)
    (width routeWidth fuel handlerTime tickTime : Nat)
    (hh : header ≤ routeWidth) (hroute : 8 * width ≤ routeWidth)
    (hrequest : recovery.recover bound.peakHeadSize ≤ width)
    (hstate : bound.peakStateSize ≤ routeWidth) (hhead : bound.peakHeadSize ≤ routeWidth)
    (hstore : ∀ n s, storeInv n s → Q.size store s ≤ routeWidth)
    (hpost : ∀ n s, storeInv n s → post s)
    (hhandler : ∀ n, Bounds control queryCost (code rep bd ports sampler store reply)
      (fun p => RequestSized (Q := Q) rep width p.1 ∧ storeInv (n + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ 8 * width ∧ storeInv n p.2) handlerTime)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (input : Input) (saved : S) (hiStore : storeInv fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (z : Run (Option Output × S))
    (hz : z ∈ support ((caller rep bd ports sampler store reply R fuel).run control queryCost (input, saved))) :
    post z.value.2 ∧ z.steps ≤ callerTime overhead routeWidth fuel
      (bound.work + 2 * bound.queries + 2) (fun _ => bound.queries) handlerTime tickTime := by
  exact caller_bound rep bd ports sampler store reply control queryCost sizes localLaws dispatchLaws mono routing R
    storeInv post width routeWidth fuel (bound.work + 2 * bound.queries + 2) handlerTime tickTime
    (fun _ => bound.queries) hh hroute hstore hpost hhandler
    (fun _ => GeneralCaller.Reachable R)
    (fun _ state hs i next hv => resource_step rep bd sizes R recovery bound hrun width hrequest state hs i next hv)
    (fun _ state hs =>
      let widths := GeneralCaller.reachable_sizes R bound hrun state hs
      ⟨widths.1.trans hstate, widths.2.trans hhead⟩)
    htick input saved (GeneralCaller.reachable_init R input) hiStore hiInput
    (GeneralCaller.budget_of_resources R bound hrun (generalReplies M G₁ randomBound) generalKind fuel input) z hz

end Signatures.Runtime.SignatureHandler
