import Proofs.Runtime.BackendCallerSize
import Proofs.Runtime.BackendCallerExecution

/-! Numeric bounds for the actual caller's routing adapters. A common width
bounds individual boundary values, including the retained state and store.
Structural costs are derived from representation and primitive cost laws.
The deliberately loose constants avoid assigning unit cost to large copies.
-/

open PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram

universe v w

/-- Contracts for the backend's control instructions, separate from the local
realizers they invoke. Loop tests retain their explicit count-dependent cost. -/
structure RoutingCostLaws (control : ControlCosts) (overhead : Nat → Nat) : Prop where
  localCall : ∀ a b, control.localCall a b ≤ overhead (a + b)
  sequence : ∀ a b, control.sequence a b ≤ overhead (a + b)
  branch : ∀ a, control.branch a ≤ overhead a
  retain : ∀ a b, control.retain a b ≤ overhead (a + b)

namespace Caller

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {I A B S : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (localLaws : LocalCostLaws Q overhead)
  (dispatchLaws : DispatchCostLaws (Q := Q) overhead) (mono : Monotone overhead)

include sizes localLaws dispatchLaws mono

theorem done_cost_of_width (state : R.machine.State) (saved : S) (output : B)
    (width : Nat) (hh : header ≤ width) (hs : Q.size R.state state ≤ width)
    (hw : Q.size store saved ≤ width) (ho : Q.size bd.out output ≤ width) :
    Q.cost (doneCode R store) (output, state, saved) ≤ 7 * overhead (32 * width) := by
  have hf := sizes.prod_le R.state store (state, saved)
  have hi := sizes.prod_le bd.out (frame R store) (output, state, saved)
  have hp := sizes.some_le bd.out output
  have hr := sizes.prod_le (StepClass.HasOption.option bd.out) store (some output, saved)
  refine ((doneBound R store localLaws dispatchLaws).cost_le (output, state, saved)).trans ?_
  dsimp only [doneBound, LocalBound.pair, LocalBound.compose, LocalBound.fst, LocalBound.snd,
    DispatchCostLaws.someBound, frame, result] at *
  calc
    _ ≤ (overhead (32 * width) + overhead (32 * width) + overhead (32 * width)) +
        (overhead (32 * width) + overhead (32 * width) + overhead (32 * width)) +
        overhead (32 * width) := by gcongr <;> apply mono <;> omega
    _ = _ := by omega

theorem cutoff_cost_of_width (state : R.machine.State) (saved : S) (i : I)
    (width : Nat) (hh : header ≤ width) (hs : Q.size R.state state ≤ width)
    (hw : Q.size store saved ≤ width) (hi : Q.size bd.pos i ≤ width) :
    Q.cost (cutoffCode R store) (i, state, saved) ≤ 5 * overhead (32 * width) := by
  have hf := sizes.prod_le R.state store (state, saved)
  have ha := sizes.prod_le bd.pos (frame R store) (i, state, saved)
  have hp := sizes.none_le bd.out
  have hr := sizes.prod_le (StepClass.HasOption.option bd.out) store (none, saved)
  refine ((cutoffBound R store localLaws dispatchLaws).cost_le (i, state, saved)).trans ?_
  dsimp only [cutoffBound, LocalBound.pair, LocalBound.compose, LocalBound.snd,
    DispatchCostLaws.noneBound, frame, result] at *
  calc
    _ ≤ overhead (32 * width) +
        (overhead (32 * width) + overhead (32 * width) + overhead (32 * width)) +
        overhead (32 * width) := by gcongr <;> apply mono <;> omega
    _ = _ := by omega

omit dispatchLaws QO QD OC in
theorem queryArgs_cost_of_width (state : R.machine.State) (saved : S) (i : I)
    (width : Nat) (hh : header ≤ width) (hs : Q.size R.state state ≤ width)
    (hw : Q.size store saved ≤ width) (hi : Q.size bd.pos i ≤ width) :
    Q.cost (queryArgsCode R store) (i, state, saved) ≤ 9 * overhead (32 * width) := by
  have hf := sizes.prod_le R.state store (state, saved)
  have ha := sizes.prod_le bd.pos (frame R store) (i, state, saved)
  have hp := sizes.prod_le bd.pos store (i, saved)
  have hr := sizes.prod_le (StepClass.HasProd.prod bd.pos store) R.state ((i, saved), state)
  refine ((queryArgsBound R store localLaws).cost_le (i, state, saved)).trans ?_
  dsimp only [queryArgsBound, LocalBound.pair, LocalBound.compose, LocalBound.fst, LocalBound.snd,
    frame] at *
  calc
    _ ≤ (overhead (32 * width) +
        (overhead (32 * width) + overhead (32 * width) + overhead (32 * width)) +
        overhead (32 * width)) +
        (overhead (32 * width) + overhead (32 * width) + overhead (32 * width)) +
        overhead (32 * width) := by gcongr <;> apply mono <;> omega
    _ = _ := by omega

omit dispatchLaws QO QD OC in
theorem resumeArgs_cost_of_width (state : R.machine.State) (saved : S) (idx : source.toPFunctor.Idx)
    (width : Nat) (hh : header ≤ width) (hs : Q.size R.state state ≤ width)
    (hw : Q.size store saved ≤ width) (hi : Q.size bd.idx idx ≤ width) :
    Q.cost (resumeArgsCode R store) ((idx, saved), state) ≤ 9 * overhead (32 * width) := by
  have hp := sizes.prod_le bd.idx store (idx, saved)
  have ha := sizes.prod_le (StepClass.HasProd.prod bd.idx store) R.state ((idx, saved), state)
  have hf := sizes.prod_le R.state bd.idx (state, idx)
  have hr := sizes.prod_le (bd.stateIdx R.state) store ((state, idx), saved)
  refine ((resumeArgsBound R store localLaws).cost_le ((idx, saved), state)).trans ?_
  dsimp only [resumeArgsBound, LocalBound.pair, LocalBound.compose, LocalBound.fst, LocalBound.snd,
    Boundary.stateIdx] at *
  calc
    _ ≤ (overhead (32 * width) +
        (overhead (32 * width) + overhead (32 * width) + overhead (32 * width)) +
        overhead (32 * width)) +
        (overhead (32 * width) + overhead (32 * width) + overhead (32 * width)) +
        overhead (32 * width) := by gcongr <;> apply mono <;> omega
    _ = _ := by omega

variable (control : ControlCosts) (controlLaws : RoutingCostLaws control overhead)

include controlLaws

omit localLaws dispatchLaws [Q.HasCategory] QP QS QO QD OC in
theorem routeControl_of_width (input : R.machine.State × S)
    (width : Nat) (hh : header ≤ width) (hs : Q.size R.state input.1 ≤ width)
    (hw : Q.size store input.2 ≤ width) (hv : Q.size bd.head (R.machine.head input.1) ≤ width) :
    routeControl R store control input ≤ 2 * overhead (32 * width) := by
  have hf := sizes.prod_le R.state store input
  have hr := sizes.distribute_le bd.out bd.pos (frame R store) (R.machine.head input.1, input)
  have hb := controlLaws.branch (routeSize R store input)
  have hc := controlLaws.sequence (Q.size (frame R store) input) (routeSize R store input)
  have h1 : overhead (routeSize R store input) ≤ overhead (32 * width) := by
    apply mono
    dsimp only [routeSize, frame, Boundary.head] at *
    omega
  have h2 : overhead (Q.size (frame R store) input + routeSize R store input) ≤
      overhead (32 * width) := by
    apply mono
    dsimp only [routeSize, frame, Boundary.head] at *
    omega
  dsimp only [routeControl]
  omega

theorem inspect_atomic_of_width (input : R.machine.State × S)
    (width : Nat) (hh : header ≤ width) (hs : Q.size R.state input.1 ≤ width)
    (hw : Q.size store input.2 ≤ width) (hv : Q.size bd.head (R.machine.head input.1) ≤ width) :
    atomicTime control (inspectCode R store) input ≤
      Q.cost R.headCode input.1 + 7 * overhead (32 * width) := by
  have hc := inspect_cost_of_caps R store sizes localLaws dispatchLaws mono input width width width hs hw hv
  have hm : overhead (3 * width + 3 * width + 2 * width + 6 * header) ≤ overhead (32 * width) :=
    mono (by omega)
  have hf := sizes.prod_le R.state store input
  have hr := sizes.distribute_le bd.out bd.pos (frame R store) (R.machine.head input.1, input)
  have hl := controlLaws.localCall (Q.size (frame R store) input) (routeSize R store input)
  have hn : overhead (Q.size (frame R store) input + routeSize R store input) ≤ overhead (32 * width) := by
    apply mono
    dsimp only [frame, routeSize, Boundary.head] at *
    omega
  dsimp only [atomicTime, routeSize] at *
  omega

theorem returnWork_of_width (state : R.machine.State) (saved : S) (output : B)
    (hv : R.machine.view state = .inl output) (width : Nat) (hh : header ≤ width)
    (hs : Q.size R.state state ≤ width) (hw : Q.size store saved ≤ width)
    (hhead : Q.size bd.head (R.machine.head state) ≤ width) :
    returnWork R store control (state, saved) output ≤
      Q.cost R.headCode state + 20 * overhead (32 * width) := by
  have hout := sizes.sum_payload_le bd.out bd.pos (.inl output)
  have ho : Q.size bd.out output ≤ width := by
    rw [R.machine.head_eq_inl_of_view hv] at hhead
    dsimp only [Boundary.head] at *
    exact hout.trans hhead
  have hi := inspect_atomic_of_width R store sizes localLaws dispatchLaws mono control controlLaws
    (state, saved) width hh hs hw hhead
  have hc := routeControl_of_width R store sizes mono control controlLaws (state, saved) width hh hs hw hhead
  have hd := done_cost_of_width R store sizes localLaws dispatchLaws mono state saved output width hh hs hw ho
  have hf := sizes.prod_le R.state store (state, saved)
  have ha := sizes.prod_le bd.out (frame R store) (output, state, saved)
  have hp := sizes.some_le bd.out output
  have hr := sizes.prod_le (StepClass.HasOption.option bd.out) store (some output, saved)
  have hx := sizes.sum_le (result (bd := bd) store) (frame R store) (.inl (some output, saved))
  have hl := controlLaws.localCall
    (Q.size (StepClass.HasProd.prod bd.out (frame R store)) (output, state, saved))
    (Q.size (result (bd := bd) store) (some output, saved))
  have hj := dispatchLaws.inl (result (bd := bd) store) (frame R store) (some output, saved)
  have hjl := controlLaws.localCall
    (Q.size (result (bd := bd) store) (some output, saved))
    (Q.size (StepClass.HasSum.sum (result (bd := bd) store) (frame R store)) (.inl (some output, saved)))
  have hjc := controlLaws.sequence
    (Q.size (StepClass.HasProd.prod bd.out (frame R store)) (output, state, saved))
    (Q.size (result (bd := bd) store) (some output, saved))
  have hm1 : overhead (Q.size (StepClass.HasProd.prod bd.out (frame R store)) (output, state, saved) +
      Q.size (result (bd := bd) store) (some output, saved)) ≤ overhead (32 * width) := by
    apply mono
    dsimp only [frame, result] at *
    omega
  have hm2 : overhead (Q.size (result (bd := bd) store) (some output, saved) +
      Q.size (StepClass.HasSum.sum (result (bd := bd) store) (frame R store)) (.inl (some output, saved))) ≤
        overhead (32 * width) := by
    apply mono
    dsimp only [frame, result, Sum.elim] at *
    omega
  dsimp only [returnWork, atomicTime] at *
  omega

theorem stopWork_of_width (state : R.machine.State) (saved : S)
    (width : Nat) (hh : header ≤ width) (hs : Q.size R.state state ≤ width)
    (hw : Q.size store saved ≤ width) (hhead : Q.size bd.head (R.machine.head state) ≤ width) :
    stopWork R store control (state, saved) ≤ Q.cost R.headCode state + 17 * overhead (32 * width) := by
  have hi := inspect_atomic_of_width R store sizes localLaws dispatchLaws mono control controlLaws
    (state, saved) width hh hs hw hhead
  have hc := routeControl_of_width R store sizes mono control controlLaws (state, saved) width hh hs hw hhead
  have hf := sizes.prod_le R.state store (state, saved)
  cases hv : R.machine.view state with
  | inl output =>
      have hout := sizes.sum_payload_le bd.out bd.pos (.inl output)
      have ho : Q.size bd.out output ≤ width := by
        rw [R.machine.head_eq_inl_of_view hv] at hhead
        exact hout.trans hhead
      have hd := done_cost_of_width R store sizes localLaws dispatchLaws mono state saved output width hh hs hw ho
      have ha := sizes.prod_le bd.out (frame R store) (output, state, saved)
      have hp := sizes.some_le bd.out output
      have hr := sizes.prod_le (StepClass.HasOption.option bd.out) store (some output, saved)
      have hl := controlLaws.localCall
        (Q.size (StepClass.HasProd.prod bd.out (frame R store)) (output, state, saved))
        (Q.size (result (bd := bd) store) (some output, saved))
      have hm : overhead (Q.size (StepClass.HasProd.prod bd.out (frame R store)) (output, state, saved) +
          Q.size (result (bd := bd) store) (some output, saved)) ≤ overhead (32 * width) := by
        apply mono
        dsimp only [frame, result] at *
        omega
      have ht : atomicTime control (doneCode R store) (output, state, saved) ≤ 8 * overhead (32 * width) := by
        dsimp only [atomicTime]
        omega
      simp only [stopWork, hv]
      dsimp only [routeControl] at hc
      dsimp only [frame] at *
      omega
  | inr request =>
      have hout := sizes.sum_payload_le bd.out bd.pos (.inr request.1)
      have ho : Q.size bd.pos request.1 ≤ width := by
        rw [R.machine.head_eq_inr_of_view hv] at hhead
        exact hout.trans hhead
      have hd := cutoff_cost_of_width R store sizes localLaws dispatchLaws mono state saved request.1 width hh hs hw ho
      have ha := sizes.prod_le bd.pos (frame R store) (request.1, state, saved)
      have hp := sizes.none_le bd.out
      have hr := sizes.prod_le (StepClass.HasOption.option bd.out) store (none, saved)
      have hl := controlLaws.localCall
        (Q.size (StepClass.HasProd.prod bd.pos (frame R store)) (request.1, state, saved))
        (Q.size (result (bd := bd) store) (none, saved))
      have hm : overhead (Q.size (StepClass.HasProd.prod bd.pos (frame R store)) (request.1, state, saved) +
          Q.size (result (bd := bd) store) (none, saved)) ≤ overhead (32 * width) := by
        apply mono
        dsimp only [frame, result] at *
        omega
      have ht : atomicTime control (cutoffCode R store) (request.1, state, saved) ≤ 8 * overhead (32 * width) := by
        dsimp only [atomicTime]
        omega
      simp only [stopWork, hv]
      dsimp only [routeControl] at hc
      dsimp only [frame] at *
      omega

theorem queryWork_of_width (state : R.machine.State) (saved saved' : S) (i : I)
    (next : source.Range i → R.machine.State) (reply : source.Range i)
    (hv : R.machine.view state = .inr ⟨i, next⟩) (width : Nat) (hh : header ≤ width)
    (hs : Q.size R.state state ≤ width) (hw : Q.size store saved ≤ width)
    (hhead : Q.size bd.head (R.machine.head state) ≤ width)
    (hn : Q.size R.state (next reply) ≤ width) (hw' : Q.size store saved' ≤ width)
    (hd : Q.size bd.idx ⟨i, reply⟩ ≤ width) :
    queryWork R store control (state, saved) i reply saved' ≤
      Q.cost R.headCode state + Q.cost R.updateCode (state, ⟨i, reply⟩) +
        42 * overhead (32 * width) := by
  have hout := sizes.sum_payload_le bd.out bd.pos (.inr i)
  have hp : Q.size bd.pos i ≤ width := by
    rw [R.machine.head_eq_inr_of_view hv] at hhead
    exact hout.trans hhead
  have hi := inspect_atomic_of_width R store sizes localLaws dispatchLaws mono control controlLaws
    (state, saved) width hh hs hw hhead
  have hc := routeControl_of_width R store sizes mono control controlLaws (state, saved) width hh hs hw hhead
  have ha := queryArgs_cost_of_width R store sizes localLaws mono state saved i width hh hs hw hp
  have hr := resumeArgs_cost_of_width R store sizes localLaws mono state saved' ⟨i, reply⟩ width hh hs hw' hd
  have hu := update_cost_of_caps R sizes localLaws dispatchLaws mono state i next reply hv width width hs hn hd
  have hum : overhead (5 * width + width + 4 * header) ≤ overhead (32 * width) := mono (by omega)
  have hf := sizes.prod_le R.state store (state, saved)
  have hargs := sizes.prod_le bd.pos (frame R store) (i, state, saved)
  have hpos := sizes.prod_le bd.pos store (i, saved)
  have hprepared := sizes.prod_le (StepClass.HasProd.prod bd.pos store) R.state ((i, saved), state)
  have hanswer := sizes.prod_le bd.idx store (⟨i, reply⟩, saved')
  have hreceived := sizes.prod_le (StepClass.HasProd.prod bd.idx store) R.state ((⟨i, reply⟩, saved'), state)
  have hupdate := sizes.prod_le R.state bd.idx (state, ⟨i, reply⟩)
  have hresume := sizes.prod_le (bd.stateIdx R.state) store ((state, ⟨i, reply⟩), saved')
  have hnext := sizes.prod_le R.state store (next reply, saved')
  have hresult := sizes.sum_le (result (bd := bd) store) (frame R store) (.inr (next reply, saved'))
  have hlocal : ∀ a b, a + b ≤ 32 * width → control.localCall a b ≤ overhead (32 * width) :=
    fun a b h => (controlLaws.localCall a b).trans (mono h)
  have hseq : ∀ a b, a + b ≤ 32 * width → control.sequence a b ≤ overhead (32 * width) :=
    fun a b h => (controlLaws.sequence a b).trans (mono h)
  have hretain : ∀ a b, a + b ≤ 32 * width → control.retain a b ≤ overhead (32 * width) :=
    fun a b h => (controlLaws.retain a b).trans (mono h)
  dsimp only [frame, Boundary.stateIdx, Sum.elim] at *
  have hla := hlocal
    (Q.size (StepClass.HasProd.prod bd.pos (frame R store)) (i, state, saved))
    (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod bd.pos store) R.state) ((i, saved), state)) (by dsimp only [frame, Boundary.stateIdx]; omega)
  have hlr := hlocal
    (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod bd.idx store) R.state) ((⟨i, reply⟩, saved'), state))
    (Q.size (StepClass.HasProd.prod (bd.stateIdx R.state) store) ((state, ⟨i, reply⟩), saved')) (by dsimp only [frame, Boundary.stateIdx]; omega)
  have hlu := hlocal (Q.size (bd.stateIdx R.state) (state, ⟨i, reply⟩)) (Q.size R.state (next reply)) (by dsimp only [frame, Boundary.stateIdx]; omega)
  have hlj := hlocal (Q.size (frame R store) (next reply, saved'))
    (Q.size (StepClass.HasSum.sum (result (bd := bd) store) (frame R store)) (.inr (next reply, saved'))) (by dsimp only [frame, Boundary.stateIdx]; omega)
  have hj := dispatchLaws.inr (result (bd := bd) store) (frame R store) (next reply, saved')
  have hjm : overhead (Q.size (frame R store) (next reply, saved') +
      Q.size (StepClass.HasSum.sum (result (bd := bd) store) (frame R store)) (.inr (next reply, saved'))) ≤
        overhead (32 * width) := mono (by dsimp only [frame, Boundary.stateIdx]; omega)
  have ht1 := hretain (Q.size R.state state) (Q.size (StepClass.HasProd.prod bd.idx store) (⟨i, reply⟩, saved')) (by dsimp only [frame, Boundary.stateIdx]; omega)
  have ht2 := hretain (Q.size store saved') (Q.size R.state (next reply)) (by omega)
  have hq1 := hseq
    (Q.size (StepClass.HasProd.prod bd.pos (frame R store)) (i, state, saved))
    (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod bd.pos store) R.state) ((i, saved), state)) (by dsimp only [frame, Boundary.stateIdx]; omega)
  have hq2 := hseq
    (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod bd.pos store) R.state) ((i, saved), state))
    (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod bd.idx store) R.state) ((⟨i, reply⟩, saved'), state)) (by dsimp only [frame, Boundary.stateIdx]; omega)
  have hq3 := hseq
    (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod bd.idx store) R.state) ((⟨i, reply⟩, saved'), state))
    (Q.size (StepClass.HasProd.prod (bd.stateIdx R.state) store) ((state, ⟨i, reply⟩), saved')) (by dsimp only [frame, Boundary.stateIdx]; omega)
  have hq4 := hseq
    (Q.size (StepClass.HasProd.prod (bd.stateIdx R.state) store) ((state, ⟨i, reply⟩), saved'))
    (Q.size (frame R store) (next reply, saved')) (by dsimp only [frame, Boundary.stateIdx]; omega)
  simp only [queryWork, atomicTime, R.machine.update?_of_view_query hv, Option.getD_some] at *
  dsimp only [frame, Boundary.stateIdx, Sum.elim] at *
  omega

omit localLaws dispatchLaws [Q.HasCategory] QP QS QO QD OC in
theorem initWork_of_width (input : A × S) (width : Nat)
    (hh : header ≤ width)
    (hs : Q.size store input.2 ≤ width)
    (hn : Q.size R.state (R.machine.init input.1) ≤ width)
    (hi : Q.size bd.input input.1 ≤ width) :
    initWork R store control input ≤ Q.cost R.initCode input.1 + 3 * overhead (32 * width) := by
  have ha := sizes.prod_le bd.input store input
  have hf := sizes.prod_le R.state store (R.machine.init input.1, input.2)
  have hl := (controlLaws.localCall (Q.size bd.input input.1) (Q.size R.state (R.machine.init input.1))).trans
    (mono (show Q.size bd.input input.1 + Q.size R.state (R.machine.init input.1) ≤ 32 * width by omega))
  have hr := (controlLaws.retain (Q.size store input.2) (Q.size R.state (R.machine.init input.1))).trans
    (mono (show Q.size store input.2 + Q.size R.state (R.machine.init input.1) ≤ 32 * width by omega))
  have hc := (controlLaws.sequence (Q.size (StepClass.HasProd.prod bd.input store) input)
      (Q.size (frame R store) (R.machine.init input.1, input.2))).trans
    (mono (show Q.size (StepClass.HasProd.prod bd.input store) input +
      Q.size (frame R store) (R.machine.init input.1, input.2) ≤ 32 * width by dsimp only [frame] at *; omega))
  dsimp only [initWork, atomicTime]
  omega

end Caller
end Signatures.Runtime.BackendProgram
