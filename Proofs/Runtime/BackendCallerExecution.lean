import Proofs.Runtime.BackendCallerCorrectness

/-! Exact cost equations for the assembled caller's local dispatch blocks.

The only effectful operation in a query iteration is the supplied handler code.
Its complete costed execution is preserved; all local code and control charges
are displayed separately. These equations allow additive whole-run accounting
without multiplying the caller's own work by its query cap.
-/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}

def atomicTime (control : ControlCosts) {A B : Type} {a : C.Str A} {b : C.Str B}
    {f : A → B} (code : Q.Realizer a b f) (input : A) : Nat :=
  Q.cost code input + control.localCall (Q.size a input) (Q.size b (f input))

namespace Caller

variable [C.HasOption] [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {I A B S J : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {target : OracleSpec J} {iface : Interface (C := C) target}
  (control : ControlCosts) (queryCost : (j : J) → target.Range j → Nat)

def routeSize (input : R.machine.State × S) : Nat :=
  Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod bd.out (frame R store))
    (StepClass.HasProd.prod bd.pos (frame R store)))
    (Sum.elim (fun value => Sum.inl (value, input)) (fun position => Sum.inr (position, input))
      (R.machine.head input.1))

def routeControl (input : R.machine.State × S) : Nat :=
  control.branch (routeSize R store input) +
    control.sequence (Q.size (frame R store) input) (routeSize R store input)

def stopWork (input : R.machine.State × S) : Nat :=
  atomicTime control (inspectCode R store) input +
    ((match R.machine.view input.1 with
    | .inl output => atomicTime control (doneCode R store) (output, input)
    | .inr request => atomicTime control (cutoffCode R store) (request.1, input)) +
      control.branch (routeSize R store input)) +
    control.sequence (Q.size (frame R store) input) (routeSize R store input)

def returnWork (input : R.machine.State × S) (output : B) : Nat :=
  atomicTime control (inspectCode R store) input + routeControl R store control input +
    atomicTime control (doneCode R store) (output, input) +
    atomicTime control (QS.inl (result (bd := bd) store) (frame R store)) (some output, input.2) +
    control.sequence (Q.size (StepClass.HasProd.prod bd.out (frame R store)) (output, input))
      (Q.size (result (bd := bd) store) (some output, input.2))

def queryWork (input : R.machine.State × S) (i : I) (reply : source.Range i) (saved : S) : Nat :=
  let idx : source.toPFunctor.Idx := ⟨i, reply⟩
  let next := (R.machine.update? (input.1, idx)).getD input.1
  let argsSize := Q.size (StepClass.HasProd.prod bd.pos (frame R store)) (i, input)
  let preparedSize := Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod bd.pos store) R.state)
    ((i, input.2), input.1)
  let handlerSize := Q.size (StepClass.HasProd.prod bd.idx store) (idx, saved)
  let receivedSize := Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod bd.idx store) R.state)
    ((idx, saved), input.1)
  let resumeSize := Q.size (StepClass.HasProd.prod (bd.stateIdx R.state) store) ((input.1, idx), saved)
  let nextSize := Q.size (frame R store) (next, saved)
  atomicTime control (inspectCode R store) input + routeControl R store control input +
    atomicTime control (queryArgsCode R store) (i, input) +
    atomicTime control (resumeArgsCode R store) ((idx, saved), input.1) +
    atomicTime control (updateCode R) (input.1, idx) +
    atomicTime control (QS.inr (result (bd := bd) store) (frame R store)) (next, saved) +
    control.retain (Q.size R.state input.1) handlerSize +
    control.retain (Q.size store saved) (Q.size R.state next) +
    control.sequence argsSize preparedSize + control.sequence preparedSize receivedSize +
    control.sequence receivedSize resumeSize + control.sequence resumeSize nextSize

omit QS in
theorem stop_run (state : R.machine.State) (saved : S) :
    (stop (target := target) (iface := iface) R store).run control queryCost (state, saved) =
      pure ⟨(match R.machine.view state with | .inl output => some output | .inr _ => none, saved),
        stopWork R store control (state, saved)⟩ := by
  cases hv : R.machine.view state with
  | inl output =>
      simp [stop, Code.run, sequenceRun, chargeRun, stopWork, routeSize, atomicTime,
        hv, R.machine.head_eq_inl_of_view hv]
  | inr request =>
      simp [stop, Code.run, sequenceRun, chargeRun, stopWork, routeSize, atomicTime,
        hv, R.machine.head_eq_inr_of_view hv]

variable (handler : Code Q target iface (StepClass.HasProd.prod bd.pos store)
  (StepClass.HasProd.prod bd.idx store))

omit QO in
theorem body_return_run (state : R.machine.State) (saved : S) (output : B)
    (hv : R.machine.view state = .inl output) :
    (body R store handler).run control queryCost (state, saved) =
      pure ⟨Sum.inl (some output, saved), returnWork R store control (state, saved) output⟩ := by
  simp [body, Code.run, sequenceRun, chargeRun, returnWork, routeControl, routeSize, atomicTime,
    R.machine.head_eq_inl_of_view hv]
  dsimp only [frame]
  omega

variable (H : GeneralCaller.Handler (spec := source) (StateT S (OracleComp target)))
  (hhandler : ∀ i saved, handler.run control queryCost (i, saved) =
    (fun p => (⟨(⟨i, p.1.value⟩, p.2), p.1.steps⟩ : Run (source.toPFunctor.Idx × S))) <$> (H i).run saved)

include hhandler

omit QO in
theorem body_query_run (state : R.machine.State) (saved : S) (i : I)
    (next : source.Range i → R.machine.State) (hv : R.machine.view state = .inr ⟨i, next⟩) :
    (body R store handler).run control queryCost (state, saved) =
      (fun p => ⟨Sum.inr (next p.1.value, p.2),
        p.1.steps + queryWork R store control (state, saved) i p.1.value p.2⟩) <$> (H i).run saved := by
  simp [body, Code.run, sequenceRun, chargeRun, retainRun, hhandler,
    queryWork, routeControl, routeSize, atomicTime, R.machine.head_eq_inr_of_view hv,
    R.machine.update?_of_view_query hv, bind_pure_comp]
  congr 1
  funext p
  congr 1
  dsimp only [frame]
  omega

omit hhandler in
def initWork (input : A × S) : Nat :=
  atomicTime control R.initCode input.1 +
    control.retain (Q.size store input.2) (Q.size R.state (R.machine.init input.1)) +
    control.sequence (Q.size (StepClass.HasProd.prod bd.input store) input)
      (Q.size (frame R store) (R.machine.init input.1, input.2))

omit hhandler in
theorem program_run (fuel : Nat) (input : A × S) :
    (program R store handler fuel).run control queryCost input =
      (fun r => ⟨r.value, r.steps + initWork R store control input⟩) <$>
        (fromState R store handler fuel).run control queryCost (R.machine.init input.1, input.2) := by
  simp [program, Code.run, sequenceRun, retainRun, atomicTime, initWork, bind_pure_comp,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end Caller
end Signatures.Runtime.BackendProgram
