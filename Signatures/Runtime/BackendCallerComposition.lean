import Signatures.Runtime.BackendCallerExecution
import Signatures.Runtime.GeneralCallerBudget

/-! Additive cost comparison for the complete assembled caller.

The reference charges the original caller's actual initialization/head/update
work and the implemented handlers' actual work. Only local dispatch/control
allowances are accumulated per iteration. No whole-solver budget is assumed.
-/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram.Caller

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {I A B S J : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {target : OracleSpec J} {iface : Interface (C := C) target}
  (control : ControlCosts) (queryCost : (j : J) → target.Range j → Nat)
  (handler : Code Q target iface (StepClass.HasProd.prod bd.pos store)
    (StepClass.HasProd.prod bd.idx store))
  (H : GeneralCaller.Handler (spec := source) (StateT S (OracleComp target)))
  (hhandler : ∀ i saved, handler.run control queryCost (i, saved) =
    (fun p => (⟨(⟨i, p.1.value⟩, p.2), p.1.steps⟩ : Run (source.toPFunctor.Idx × S))) <$> (H i).run saved)
  (inv : R.machine.State × S → Prop) (routingTime tickTime : Nat)
  (hstep : ∀ state saved, inv (state, saved) → ∀ i next,
    R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved), inv (next p.1.value, p.2))
  (hstop : ∀ state saved, inv (state, saved) →
    stopWork R store control (state, saved) ≤ Q.cost R.headCode state + routingTime)
  (hreturn : ∀ state saved, inv (state, saved) → ∀ output,
    R.machine.view state = .inl output →
      returnWork R store control (state, saved) output ≤ Q.cost R.headCode state + routingTime)
  (hquery : ∀ state saved, inv (state, saved) → ∀ i next,
    R.machine.view state = .inr ⟨i, next⟩ → ∀ p ∈ support ((H i).run saved),
      queryWork R store control (state, saved) i p.1.value p.2 ≤
        Q.cost R.headCode state + Q.cost R.updateCode (state, ⟨i, p.1.value⟩) + routingTime)

include hhandler hstep hstop hreturn hquery

theorem fromState_refines_cost (fuel : Nat)
    (htick : ∀ n ≤ fuel, ∀ state saved, inv (state, saved) →
      control.loop n (Q.size (frame R store) (state, saved)) ≤ tickTime)
    (state : R.machine.State) (saved : S) (hi : inv (state, saved))
    (z : Run (Option B × S))
    (hz : z ∈ support ((fromState R store handler fuel).run control queryCost (state, saved))) :
    ∃ reference ∈ support ((GeneralCaller.runFrom R H fuel state).run saved),
      z.value = (reference.1.value, reference.2) ∧
        z.steps ≤ reference.1.steps + (fuel + 1) * (routingTime + tickTime) := by
  induction fuel generalizing state saved z with
  | zero =>
      change z ∈ support (chargeRun (control.loop 0 (Q.size (frame R store) (state, saved)))
        ((stop R store).run control queryCost (state, saved))) at hz
      rw [stop_run R store control queryCost] at hz
      simp only [chargeRun, map_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      refine ⟨(⟨match R.machine.view state with | .inl output => some output | .inr _ => none,
        Q.cost R.headCode state + 1⟩, saved), ?_, ?_, ?_⟩
      · cases hv : R.machine.view state <;> simp [GeneralCaller.runFrom, StateT.run_pure, hv]
      · cases R.machine.view state <;> rfl
      · have hs := hstop state saved hi
        have hc := htick 0 le_rfl state saved hi
        dsimp
        omega
  | succ fuel ih =>
      rw [fromState, Code.run, loopRun] at hz
      cases hv : R.machine.view state with
      | inl output =>
          rw [body_return_run R store control queryCost handler state saved output hv] at hz
          simp only [pure_bind, support_pure, Set.mem_singleton_iff] at hz
          subst z
          refine ⟨(⟨some output, Q.cost R.headCode state + 1⟩, saved), ?_, rfl, ?_⟩
          · simp [GeneralCaller.runFrom, hv, StateT.run_pure]
          · have hs := hreturn state saved hi output hv
            have hc := htick (fuel + 1) le_rfl state saved hi
            dsimp
            nlinarith
      | inr request =>
          rcases request with ⟨i, next⟩
          rw [body_query_run R store control queryCost handler H hhandler state saved i next hv] at hz
          simp only [bind_map_left, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨p, hp, rest, hr, rfl⟩ := hz
          obtain ⟨reference, href, hvalue, hcost⟩ := ih (fun n hn => htick n (by omega))
            (next p.1.value) p.2 (hstep state saved hi i next hv p hp) rest hr
          refine ⟨(⟨reference.1.value, Q.cost R.headCode state + p.1.steps +
            Q.cost R.updateCode (state, ⟨i, p.1.value⟩) + reference.1.steps + 2⟩, reference.2),
            ?_, hvalue, ?_⟩
          · simp only [GeneralCaller.runFrom, hv, StateT.run_bind, StateT.run_pure,
              mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
            exact ⟨p, hp, reference, href, rfl⟩
          · have hs := hquery state saved hi i next hv p hp
            have hc := htick (fuel + 1) le_rfl state saved hi
            dsimp
            nlinarith

theorem program_refines_cost (fuel initialTime : Nat)
    (htick : ∀ n ≤ fuel, ∀ state saved, inv (state, saved) →
      control.loop n (Q.size (frame R store) (state, saved)) ≤ tickTime)
    (input : A × S) (hi : inv (R.machine.init input.1, input.2))
    (hinit : initWork R store control input ≤ Q.cost R.initCode input.1 + initialTime)
    (z : Run (Option B × S))
    (hz : z ∈ support ((program R store handler fuel).run control queryCost input)) :
    ∃ reference ∈ support ((GeneralCaller.run R H fuel input.1).run input.2),
      z.value = (reference.1.value, reference.2) ∧
        z.steps ≤ reference.1.steps + initialTime + (fuel + 1) * (routingTime + tickTime) := by
  rw [program_run R store control queryCost handler, support_map] at hz
  obtain ⟨rest, hr, rfl⟩ := hz
  obtain ⟨reference, href, hvalue, hcost⟩ := fromState_refines_cost R store control queryCost handler H hhandler
    inv routingTime tickTime hstep hstop hreturn hquery fuel htick _ _ hi rest hr
  refine ⟨(⟨reference.1.value, Q.cost R.initCode input.1 + reference.1.steps + 1⟩, reference.2),
    ?_, hvalue, ?_⟩
  · simp only [GeneralCaller.run, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    exact ⟨reference, href, rfl⟩
  · dsimp
    omega

end Signatures.Runtime.BackendProgram.Caller
