import Signatures.Runtime.BackendCaller

/-! Exact correctness of the finite caller/handler assembly. The handler
certificate describes one request; adaptive composition and fuel handling are
proved here for the constructed program. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.BackendProgram.Caller

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum] [QO : Q.HasOption]
  [QD : Q.IsDistributive] [OC : OptionCode (Q := Q)]
  {I A B S J : Type} {source : OracleSpec I} [DecidableEq I]
  {bd : Boundary C source.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd)) (store : C.Str S)
  {target : OracleSpec J} {iface : Interface (C := C) target}
  (handler : Code Q target iface (StepClass.HasProd.prod bd.pos store)
    (StepClass.HasProd.prod bd.idx store))

omit QO in
theorem body_return (state : R.machine.State) (saved : S) (output : B)
    (hv : R.machine.view state = .inl output) :
    (body R store handler).denote (state, saved) = pure (.inl (some output, saved)) := by
  simp [body, Code.denote, R.machine.head_eq_inl_of_view hv]

omit QS in
theorem stop_return (state : R.machine.State) (saved : S) (output : B)
    (hv : R.machine.view state = .inl output) :
    (stop (target := target) (iface := iface) R store).denote (state, saved) =
      pure (some output, saved) := by
  simp [stop, Code.denote, R.machine.head_eq_inl_of_view hv]

omit QS in
theorem stop_query (state : R.machine.State) (saved : S)
    (i : I) (next : source.Range i → R.machine.State)
    (hv : R.machine.view state = .inr ⟨i, next⟩) :
    (stop (target := target) (iface := iface) R store).denote (state, saved) =
      pure (none, saved) := by
  simp [stop, Code.denote, R.machine.head_eq_inr_of_view hv]

variable (H : QueryImpl source (StateT S (OracleComp target)))
  (hhandler : ∀ i saved, handler.denote (i, saved) =
    (fun p => (⟨i, p.1⟩, p.2)) <$> (H i).run saved)

include hhandler

omit QO in
theorem body_query (state : R.machine.State) (saved : S)
    (i : I) (next : source.Range i → R.machine.State)
    (hv : R.machine.view state = .inr ⟨i, next⟩) :
    (body R store handler).denote (state, saved) =
      (fun p => Sum.inr (next p.1, p.2)) <$> (H i).run saved := by
  simp [body, Code.denote, R.machine.head_eq_inr_of_view hv, hhandler,
    R.machine.update?_of_view_query hv, bind_pure_comp]

/-- The constructed loop exactly runs the general caller, preserving the
wrapper state and the optional cutoff result on every adaptive branch. -/
theorem fromState_denote (fuel : Nat) (state : R.machine.State) (saved : S) :
    (fromState R store handler fuel).denote (state, saved) =
      (GeneralCaller.denoteFrom R H fuel state).run saved := by
  induction fuel generalizing state saved with
  | zero =>
      change (stop R store).denote (state, saved) = _
      cases hv : R.machine.view state with
      | inl output =>
          rw [stop_return R store state saved output hv]
          simp [GeneralCaller.denoteFrom, hv]
      | inr request =>
          rcases request with ⟨i, next⟩
          rw [stop_query R store state saved i next hv]
          simp [GeneralCaller.denoteFrom, hv]
  | succ fuel ih =>
      change loopDenote (body R store handler).denote (stop R store).denote (fuel + 1)
        (state, saved) = _
      rw [loopDenote]
      cases hv : R.machine.view state with
      | inl output =>
          rw [body_return R store handler state saved output hv]
          simp [GeneralCaller.denoteFrom, hv]
      | inr request =>
          rcases request with ⟨i, next⟩
          rw [body_query R store handler H hhandler state saved i next hv]
          simp only [bind_map_left, GeneralCaller.denoteFrom, hv, StateT.run_bind]
          congr 1
          funext p
          exact ih (next p.1) p.2

theorem program_denote (fuel : Nat) (input : A) (saved : S) :
    (program R store handler fuel).denote (input, saved) =
      (R.machine.runWithInput H fuel input).run saved := by
  simp only [program, Code.denote, map_pure, pure_bind]
  rw [fromState_denote R store handler H hhandler fuel]
  rw [GeneralCaller.denoteFrom_eq_runWith]
  rfl

/-- Actual target program data is constructed by `Backend.compile`. Its
semantic correctness follows from the generic component contracts. -/
theorem compiled_program_erase (control : ControlCosts)
    (queryCost : (j : J) → target.Range j → Nat)
    (backend : Backend.{v, w, x} Q target iface control queryCost)
    (fuel : Nat) (input : A) (saved : S)
    (sourceProgram : A → OracleComp source B)
    (hsource : R.machine.ImplementsWithin sourceProgram fuel) :
    Run.value <$> backend.execute (backend.compile (program R store handler fuel)) (input, saved) =
      (some <$> simulateQ H (sourceProgram input)).run saved := by
  rw [backend.compile_erase, program_denote R store handler H hhandler]
  rw [hsource.simulateQ_run_eq]

end Signatures.Runtime.BackendProgram.Caller
