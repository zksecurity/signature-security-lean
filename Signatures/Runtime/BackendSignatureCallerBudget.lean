import Signatures.Runtime.BackendSignatureHandlerBudget
import Signatures.Runtime.BackendCallerIndexedResource

/-! Resource substitution for a general caller using native signature dispatch.
The attacker contributes its own realized local-work and query budget. The
wrapper contributes its proved per-request cost and charged routing/control.
Store invariants may reserve capacity for the remaining adaptive requests. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SignatureHandler

open BackendProgram Coron

def callerTime (overhead : Nat → Nat) (routeWidth fuel localTime : Nat)
    (queries : Fin 3 → Nat) (handlerTime tickTime : Nat) : Nat :=
  localTime + (∑ k, queries k * handlerTime) + 3 * overhead (32 * routeWidth) +
    (fuel + 1) * (42 * overhead (32 * routeWidth) + tickTime)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {F G₁ G₂ M Input Output S : Type} [Zero G₁] [DecidableEq M] {randomBound : Nat}
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (bd : Boundary C (generalSpec M G₁ randomBound).toPFunctor Input Output)
  (ports : NativePorts (Q := Q) rep bd) (sampler : BoundedSampler rep bd ports (iface := iface))
  (store : C.Str S)
  (reply : (signing : Bool) → Code Q unifSpec iface
    (StepClass.HasProd.prod (rep.ty message) store) (StepClass.HasProd.prod (rep.ty point₁) store))
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

omit [C.HasOption] QS QO OC in
theorem executed_mem_code (i : GeneralRequest M randomBound) (saved : S)
    (z : Run ((generalSpec M G₁ randomBound).Range i) × S)
    (hz : z ∈ support ((executed rep bd ports sampler store reply control queryCost i).run saved)) :
    (⟨(⟨i, z.1.value⟩, z.2), z.1.steps⟩ : Run (GeneralIndex M G₁ randomBound × S)) ∈
      support ((code rep bd ports sampler store reply).run control queryCost (i, saved)) := by
  rw [code_executed_run, support_map]
  exact ⟨z, hz, rfl⟩

variable {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead)
  (mono : Monotone overhead) (routing : RoutingCostLaws control overhead)
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

include sizes localLaws dispatchLaws mono routing

theorem caller_bound (storeInv : Nat → S → Prop) (post : S → Prop)
    (width routeWidth fuel localTime handlerTime tickTime : Nat) (queries : Fin 3 → Nat)
    (hh : header ≤ routeWidth) (hroute : 8 * width ≤ routeWidth)
    (hstore : ∀ n s, storeInv n s → Q.size store s ≤ routeWidth)
    (hpost : ∀ n s, storeInv n s → post s)
    (hhandler : ∀ n, Bounds control queryCost (code rep bd ports sampler store reply)
      (fun p => RequestSized (Q := Q) rep width p.1 ∧ storeInv (n + 1) p.2)
      (fun p => Q.size bd.idx p.1 ≤ 8 * width ∧ storeInv n p.2) handlerTime)
    (callerInv : Nat → R.machine.State → Prop)
    (hcallerStep : ∀ n state, callerInv (n + 1) state → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ →
        RequestSized (Q := Q) rep width i ∧ ∀ answer, callerInv n (next answer))
    (hcallerWidth : ∀ n state, callerInv n state →
      Q.size R.state state ≤ routeWidth ∧ Q.size bd.head (R.machine.head state) ≤ routeWidth)
    (htick : ∀ n ≤ fuel, ∀ encoded ≤ 3 * routeWidth, control.loop n encoded ≤ tickTime)
    (input : Input) (saved : S)
    (hiCaller : callerInv fuel (R.machine.init input)) (hiStore : storeInv fuel saved)
    (hiInput : Q.size bd.input input ≤ routeWidth)
    (hbudget : GeneralCaller.Budget R (generalReplies M G₁ randomBound) generalKind fuel input localTime queries)
    (z : Run (Option Output × S))
    (hz : z ∈ support ((caller rep bd ports sampler store reply R fuel).run control queryCost (input, saved))) :
    post z.value.2 ∧ z.steps ≤ callerTime overhead routeWidth fuel localTime queries handlerTime tickTime := by
  let H := executed rep bd ports sampler store reply control queryCost
  let inv := fun n (p : R.machine.State × S) => n ≤ fuel ∧ callerInv n p.1 ∧ storeInv n p.2
  have hstep : ∀ n state saved, inv (n + 1) (state, saved) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
        inv n (next p.1.value, p.2) ∧ (generalReplies M G₁ randomBound).allows i p.1.value ∧ p.1.steps ≤ handlerTime := by
    intro n state saved hi i next hv p hp
    obtain ⟨hrequest, hnext⟩ := hcallerStep n state hi.2.1 i next hv
    have hmem := executed_mem_code rep bd ports sampler store reply control queryCost i saved p hp
    have h := hhandler n (i, saved) ⟨hrequest, hi.2.2⟩ _ hmem
    exact ⟨⟨by have := hi.1; omega, hnext p.1.value, h.1.2⟩, trivial, h.2⟩
  have hfinal : ∀ n state saved, inv n (state, saved) → post saved :=
    fun n _ saved hi => hpost n saved hi.2.2
  have hwidth : ∀ n state saved, inv n (state, saved) →
      Q.size R.state state ≤ routeWidth ∧ Q.size store saved ≤ routeWidth ∧
      Q.size bd.head (R.machine.head state) ≤ routeWidth := by
    intro n state saved hi
    obtain ⟨hstate, hhead⟩ := hcallerWidth n state hi.2.1
    exact ⟨hstate, hstore n saved hi.2.2, hhead⟩
  have hreply : ∀ n state saved, inv (n + 1) (state, saved) → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
        Q.size bd.idx ⟨i, p.1.value⟩ ≤ routeWidth := by
    intro n state saved hi i next hv p hp
    have hrequest := (hcallerStep n state hi.2.1 i next hv).1
    have hmem := executed_mem_code rep bd ports sampler store reply control queryCost i saved p hp
    exact (hhandler n (i, saved) ⟨hrequest, hi.2.2⟩ _ hmem).1.1.trans hroute
  have hloop : ∀ n state saved, inv n (state, saved) →
      control.loop n (Q.size (Caller.frame R store) (state, saved)) ≤ tickTime := by
    intro n state saved hi
    obtain ⟨hstate, hsaved, _⟩ := hwidth n state saved hi
    have hp := sizes.prod_le R.state store (state, saved)
    dsimp only at hp
    exact htick n hi.1 _ (by dsimp only [Caller.frame]; omega)
  exact Caller.assembled_bound_indexed_of_width R store control queryCost
    (code rep bd ports sampler store reply) H
    (code_executed_run rep bd ports sampler store reply control queryCost)
    (generalReplies M G₁ randomBound) generalKind (fun _ => handlerTime) inv post tickTime
    hstep hfinal hloop sizes localLaws dispatchLaws mono routing routeWidth fuel localTime queries hh
    hwidth hreply (input, saved) ⟨le_rfl, hiCaller, hiStore⟩ hiInput hbudget z hz

end Signatures.Runtime.SignatureHandler
