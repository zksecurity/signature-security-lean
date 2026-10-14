import Signatures.Runtime.BackendCallerCost
import Signatures.Runtime.BackendSize

/-! Size-derived costs for inspecting and resuming a general caller.

Only the caller's represented state/readout/reply and the wrapper store occur in
these bounds. The local caller computation retains its own backend charge. This
is a boundary-overhead result, not a bound on arbitrary attacker computation.
-/

open PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram.Caller

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {I A B S : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {header : Nat} (sizes : SizeLaws Q header)

include sizes

omit [Q.HasCategory] QP QS QO QD OC in
theorem inspectSizes_le (input : R.machine.State × S) (n : Nat)
    (hn : n ∈ inspectSizes R store input) :
    n ≤ 3 * Q.size R.state input.1 + 3 * Q.size store input.2 +
      2 * Q.size bd.head (R.machine.head input.1) + 6 * header := by
  have hf := sizes.prod_le R.state store input
  have hp := sizes.prod_le bd.head (frame R store) (R.machine.head input.1, input)
  have hr := sizes.distribute_le bd.out bd.pos (frame R store) (R.machine.head input.1, input)
  simp only [inspectSizes, List.mem_cons, List.not_mem_nil, or_false] at hn
  dsimp only [frame, Boundary.head] at hn hf hp hr ⊢
  rcases hn with h | h | h | h | h | h <;> omega

omit [Q.HasCategory] QP QS QO QD OC in
theorem updateSizes_le (input : R.machine.State × source.toPFunctor.Idx) (n : Nat)
    (hn : n ∈ updateSizes R input) :
    n ≤ 3 * Q.size R.state input.1 + Q.size bd.idx input.2 +
      2 * Q.size (StepClass.HasOption.option R.state) (R.machine.update? input) + 2 * header := by
  have hi := sizes.prod_le R.state bd.idx input
  have hp := sizes.prod_le (StepClass.HasOption.option R.state) R.state (R.machine.update? input, input.1)
  have ho := sizes.getD_le R.state (R.machine.update? input, input.1)
  simp only [updateSizes, List.mem_cons, List.not_mem_nil, or_false] at hn
  dsimp only [Boundary.stateIdx] at hn hi hp ho ⊢
  rcases hn with h | h | h | h <;> omega

variable {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead) (mono : Monotone overhead)

include localLaws dispatchLaws mono

/-- A concrete additional inspection charge from encoded-size laws. Bounds on
the original state/readout and store therefore give a bound on routing overhead. -/
theorem inspect_cost_of_sizes (input : R.machine.State × S) :
    Q.cost (inspectCode R store) input ≤ Q.cost R.headCode input.1 +
      6 * overhead (3 * Q.size R.state input.1 + 3 * Q.size store input.2 +
        2 * Q.size bd.head (R.machine.head input.1) + 6 * header) := by
  apply inspect_cost_le R store localLaws dispatchLaws
  · exact inspectSizes_le R store sizes input
  · exact fun _ h => mono h

/-- The update result is still an option here; the matching-reply invariant
identifies its payload with the next caller state in a complete execution. -/
theorem update_cost_of_sizes (input : R.machine.State × source.toPFunctor.Idx) :
    Q.cost (updateCode R) input ≤ Q.cost R.updateCode input +
      4 * overhead (3 * Q.size R.state input.1 + Q.size bd.idx input.2 +
        2 * Q.size (StepClass.HasOption.option R.state) (R.machine.update? input) + 2 * header) := by
  apply update_cost_le R localLaws dispatchLaws
  · exact updateSizes_le R sizes input
  · exact fun _ h => mono h

/-- On an actual query transition, the optional update's size is bounded by
the next state plus its header. These are precisely the caller's trace values. -/
theorem update_cost_of_transition (state : R.machine.State) (i : I)
    (next : source.Range i → R.machine.State) (reply : source.Range i)
    (hv : R.machine.view state = .inr ⟨i, next⟩) :
    Q.cost (updateCode R) (state, ⟨i, reply⟩) ≤ Q.cost R.updateCode (state, ⟨i, reply⟩) +
      4 * overhead (3 * Q.size R.state state + Q.size bd.idx ⟨i, reply⟩ +
        2 * Q.size R.state (next reply) + 4 * header) := by
  have h := update_cost_of_sizes R sizes localLaws dispatchLaws mono (state, ⟨i, reply⟩)
  rw [R.machine.update?_of_view_query hv] at h
  have hs := sizes.some_le R.state (next reply)
  have hm := mono (show 3 * Q.size R.state state + Q.size bd.idx ⟨i, reply⟩ +
      2 * Q.size (StepClass.HasOption.option R.state) (some (next reply)) + 2 * header ≤
        3 * Q.size R.state state + Q.size bd.idx ⟨i, reply⟩ +
          2 * Q.size R.state (next reply) + 4 * header by omega)
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hm) _)

theorem inspect_cost_of_caps (input : R.machine.State × S)
    (stateSize storeSize headSize : Nat)
    (hs : Q.size R.state input.1 ≤ stateSize) (hw : Q.size store input.2 ≤ storeSize)
    (hh : Q.size bd.head (R.machine.head input.1) ≤ headSize) :
    Q.cost (inspectCode R store) input ≤ Q.cost R.headCode input.1 +
      6 * overhead (3 * stateSize + 3 * storeSize + 2 * headSize + 6 * header) := by
  have h := inspect_cost_of_sizes R store sizes localLaws dispatchLaws mono input
  have hm := mono (show 3 * Q.size R.state input.1 + 3 * Q.size store input.2 +
      2 * Q.size bd.head (R.machine.head input.1) + 6 * header ≤
        3 * stateSize + 3 * storeSize + 2 * headSize + 6 * header by omega)
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hm) _)

theorem update_cost_of_caps (state : R.machine.State) (i : I)
    (next : source.Range i → R.machine.State) (reply : source.Range i)
    (hv : R.machine.view state = .inr ⟨i, next⟩) (stateSize replySize : Nat)
    (hs : Q.size R.state state ≤ stateSize) (hn : Q.size R.state (next reply) ≤ stateSize)
    (hr : Q.size bd.idx ⟨i, reply⟩ ≤ replySize) :
    Q.cost (updateCode R) (state, ⟨i, reply⟩) ≤ Q.cost R.updateCode (state, ⟨i, reply⟩) +
      4 * overhead (5 * stateSize + replySize + 4 * header) := by
  have h := update_cost_of_transition R sizes localLaws dispatchLaws mono state i next reply hv
  have hm := mono (show 3 * Q.size R.state state + Q.size bd.idx ⟨i, reply⟩ +
      2 * Q.size R.state (next reply) + 4 * header ≤
        5 * stateSize + replySize + 4 * header by omega)
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hm) _)

end Signatures.Runtime.BackendProgram.Caller
