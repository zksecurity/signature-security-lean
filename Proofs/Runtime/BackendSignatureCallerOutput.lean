import Proofs.Runtime.BackendSignatureCallerResources
import Proofs.Runtime.GeneralCallerOutput

/-! Transfer measured output bounds to actual native caller execution. The
whole returned encoding is bounded, even at the final zero-fuel readout. Exact
source correspondence follows from the caller's own termination/resource bound.
These semantic transfers do not substitute source costs for native costs. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.SignatureHandler

open BackendProgram Coron

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
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] PFunctor.Idx

theorem caller_reference_denote (fuel : Nat) (input : Input) (saved : S) :
    (caller rep bd ports sampler store reply R fuel).denote (input, saved) =
      (fun p => (p.1.value, p.2)) <$>
        ((GeneralCaller.run R (executed rep bd ports sampler store reply control queryCost) fuel input).run saved) := by
  have hhandler : (fun i => Run.value <$> executed rep bd ports sampler store reply control queryCost i) =
      source rep store reply := by
    funext i saved
    change (Run.value <$> executed rep bd ports sampler store reply control queryCost i).run saved = _
    rw [StateT.run_map]
    exact executed_erase rep bd ports sampler store reply control queryCost i saved
  rw [caller_denote]
  have h := congrArg (fun computation => computation.run saved)
    (GeneralCaller.runFrom_erase R (executed rep bd ports sampler store reply control queryCost)
      fuel (R.machine.init input))
  rw [hhandler, GeneralCaller.denoteFrom_eq_runWith] at h
  simp only [runWithInput, GeneralCaller.run, bind_pure_comp, StateT.run_map, Functor.map_map] at h ⊢
  exact h.symm

theorem caller_output_invariant (inv : Nat → R.machine.State → Prop) (valid : Output → Prop)
    (hstep : ∀ n state, inv (n + 1) state → ∀ i next,
      R.machine.view state = .inr ⟨i, next⟩ → ∀ answer, inv n (next answer))
    (hreturn : ∀ n state, inv n state → ∀ out, R.machine.view state = .inl out → valid out)
    (fuel : Nat) (input : Input) (hi : inv fuel (R.machine.init input)) (saved : S)
    (z : Run (Option Output × S))
    (hz : z ∈ support ((caller rep bd ports sampler store reply R fuel).run control queryCost (input, saved)))
    (out : Output) (hout : z.value.1 = some out) : valid out := by
  have hv := Code.value_mem_denote control queryCost
    (caller rep bd ports sampler store reply R fuel) (input, saved) z hz
  rw [caller_reference_denote rep bd ports sampler store reply control queryCost R, support_map] at hv
  obtain ⟨p, hp, he⟩ := hv
  exact GeneralCaller.run_output_invariant R (executed rep bd ports sampler store reply control queryCost)
    inv valid hstep hreturn fuel input hi saved p hp out ((congrArg Prod.fst he).trans hout)

variable (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))

include hrun

theorem caller_output_size_of_resources {header : Nat} (sizes : SizeLaws Q header)
    (fuel : Nat) (input : Input) (saved : S) (z : Run (Option Output × S))
    (hz : z ∈ support ((caller rep bd ports sampler store reply R fuel).run control queryCost (input, saved)))
    (out : Output) (hout : z.value.1 = some out) : Q.size bd.out out ≤ bound.peakHeadSize := by
  exact caller_output_invariant rep bd ports sampler store reply control queryCost R
    (fun _ => GeneralCaller.Reachable R) (fun out => Q.size bd.out out ≤ bound.peakHeadSize)
    (fun _ state hs i next hv answer => GeneralCaller.reachable_step R state hs i next hv answer)
    (fun _ state hs out hv => reachable_output bd sizes R bound hrun state hs out hv)
    fuel input (GeneralCaller.reachable_init R input) saved z hz out hout

omit [Zero G₁] in
theorem caller_source_of_resources (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (generalSpec M G₁ randomBound) Output)
    (hprogram : R.machine.Implements program) (input : Input) (saved : S) :
    (caller rep bd ports sampler store reply R fuel).denote (input, saved) =
      (some <$> simulateQ (source rep store reply) (program input)).run saved := by
  rw [caller_denote]
  rw [(GeneralCaller.implementsWithin_of_resources R bound hrun program hprogram fuel hfuel).simulateQ_run_eq
    (source rep store reply) input]

omit [Zero G₁] in
theorem caller_no_cutoff_of_resources (fuel : Nat) (hfuel : bound.queries ≤ fuel)
    (program : Input → OracleComp (generalSpec M G₁ randomBound) Output)
    (hprogram : R.machine.Implements program) (input : Input) (saved : S)
    (z : Run (Option Output × S))
    (hz : z ∈ support ((caller rep bd ports sampler store reply R fuel).run control queryCost (input, saved))) :
    ∃ out, z.value.1 = some out := by
  have hv := Code.value_mem_denote control queryCost
    (caller rep bd ports sampler store reply R fuel) (input, saved) z hz
  rw [caller_source_of_resources rep bd ports sampler store reply R bound hrun fuel hfuel program hprogram,
    StateT.run_map, support_map] at hv
  obtain ⟨p, _, he⟩ := hv
  exact ⟨p.1, (congrArg Prod.fst he).symm⟩

end Signatures.Runtime.SignatureHandler
