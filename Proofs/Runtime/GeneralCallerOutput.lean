import Proofs.Runtime.GeneralCaller

/-! Output invariants for general costed callers. The invariant follows the
remaining execution fuel and every possible reply-dependent continuation. It
bounds a returned value even when the final readout occurs at zero remaining
fuel; an actual cutoff remains absent. Handler execution costs are unchanged. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.GeneralCaller

variable {I A B J S : Type} {spec : OracleSpec I} {target : OracleSpec J}
  {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq I] {Q : QuantitativeStepClass C}
  {bd : Boundary C spec.toPFunctor A B}
  (R : Caller (Q := Q) (bd := bd))
  (H : Handler (spec := spec) (StateT S (OracleComp target)))
  (inv : Nat → R.machine.State → Prop) (valid : B → Prop)
  (hstep : ∀ n state, inv (n + 1) state → ∀ i next,
    R.machine.view state = .inr ⟨i, next⟩ → ∀ reply, inv n (next reply))
  (hreturn : ∀ n state, inv n state → ∀ output, R.machine.view state = .inl output → valid output)

include hstep hreturn

theorem runFrom_output_invariant (fuel : Nat) (state : R.machine.State) (hi : inv fuel state)
    (saved : S) (z : Run (Option B) × S)
    (hz : z ∈ support ((runFrom R H fuel state).run saved))
    (output : B) (hout : z.1.value = some output) : valid output := by
  induction fuel generalizing state saved z with
  | zero =>
      simp only [runFrom, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      cases hv : R.machine.view state with
      | inl result =>
          have he : result = output := by simpa only [hv, Option.some.injEq] using hout
          subst result
          exact hreturn 0 state hi output hv
      | inr request => simp [hv] at hout
  | succ fuel ih =>
      cases hv : R.machine.view state with
      | inl result =>
          simp only [runFrom, hv, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
          subst z
          have he : result = output := by simpa only [Option.some.injEq] using hout
          subst result
          exact hreturn (fuel + 1) state hi output hv
      | inr request =>
          rcases request with ⟨i, next⟩
          simp only [runFrom, hv, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
            support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨answer, ha, rest, hr, rfl⟩ := hz
          exact ih (next answer.1.value) (hstep fuel state hi i next hv answer.1.value) answer.2 rest hr hout

theorem run_output_invariant (fuel : Nat) (input : A) (hi : inv fuel (R.machine.init input))
    (saved : S) (z : Run (Option B) × S)
    (hz : z ∈ support ((run R H fuel input).run saved))
    (output : B) (hout : z.1.value = some output) : valid output := by
  simp only [run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨rest, hr, rfl⟩ := hz
  exact runFrom_output_invariant R H inv valid hstep hreturn fuel _ hi saved rest hr output hout

end Signatures.Runtime.GeneralCaller
