import Signatures.Runtime.BackendStateSimulationExecution
import VCVio.OracleComp.SimSemantics.StateT.Basic.Native

/-! The source marginal of joint native/profile instrumentation. It is exactly
the original program's profile under the implemented handler, including the
joint output and simulator state. Source resource bounds therefore apply to
the profiles paired with actual native runs, without a distribution-only gap. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.StateSimulation

universe v w

def auditView {I B S : Type} (z : Audit I B S) : ExecutionProfile.Result I B × S :=
  ((z.1.value.1, z.2), z.1.value.2)

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QD : Q.IsDistributive]
  {I J S : Type} {source : OracleSpec I} {target : OracleSpec J}
  {src : Interface (C := C) source} {dst : Interface (C := C) target}
  (store : C.Str S) (control : ControlCosts)
  (queryCost : (j : J) → target.Range j → Nat)
  (handler : Code Q target dst (StepClass.HasProd.prod src.position store)
    (StepClass.HasProd.prod src.response store))
  (H : QueryImpl source (StateT S (OracleComp target)))

omit [Q.HasCategory] QP in
theorem auditLoop_source {A B : Type} (a : C.Str A) (b : C.Str B)
    (body : A × S → OracleComp target (Audit I (B ⊕ A) S))
    (stop : A × S → OracleComp target (Audit I B S))
    (originalBody : A → OracleComp source (ExecutionProfile.Result I (B ⊕ A)))
    (originalStop : A → OracleComp source (ExecutionProfile.Result I B))
    (hbody : ∀ input saved, auditView <$> body (input, saved) = (simulateQ H (originalBody input)).run saved)
    (hstop : ∀ input saved, auditView <$> stop (input, saved) = (simulateQ H (originalStop input)).run saved)
    (fuel : Nat) (input : A) (saved : S) :
    auditView <$> auditLoop (Q := Q) store control a b body stop fuel (input, saved) =
      (simulateQ H (ExecutionProfile.loop (Q := Q) a b originalBody originalStop fuel input)).run saved := by
  induction fuel generalizing input saved with
  | zero =>
      simp only [auditLoop, ExecutionProfile.loop, simulateQ_map, StateT.run_map, ← hstop, Functor.map_map]
      rfl
  | succ fuel ih =>
      simp only [auditLoop, ExecutionProfile.loop, map_bind, simulateQ_bind, StateT.run_bind,
        ← hbody, bind_map_left]
      congr 1
      funext z
      cases h : z.1.value.1 with
      | inl result =>
          simp only [auditView, h, simulateQ_pure, StateT.run_pure, map_pure]
          rfl
      | inr next =>
          simp only [auditView, h, bind_pure_comp, simulateQ_map, StateT.run_map, ← ih, Functor.map_map]
          rfl

omit QD [C.HasSum] [Q.HasCategory] QP in
theorem auditIteration_source {A : Type} (a : C.Str A) (counter : C.Str Nat)
    (body : A × S → OracleComp target (Audit I A S))
    (original : A → OracleComp source (ExecutionProfile.Result I A))
    (hbody : ∀ input saved, auditView <$> body (input, saved) = (simulateQ H (original input)).run saved)
    (count : Nat) (input : A) (saved : S) :
    auditView <$> auditIteration (Q := Q) store control a counter body count (input, saved) =
      (simulateQ H (ExecutionProfile.iteration (Q := Q) a counter original count input)).run saved := by
  induction count generalizing input saved with
  | zero => rfl
  | succ count ih =>
      simp only [auditIteration, ExecutionProfile.iteration, map_bind, simulateQ_bind, StateT.run_bind,
        ← hbody, bind_map_left]
      congr 1
      funext z
      simp only [auditView, map_pure, simulateQ_pure, StateT.run_pure,
        bind_pure_comp, ← ih, Functor.map_map]
      rfl

theorem audit_source
    (hhandler : ∀ i saved, handler.denote (i, saved) =
      (fun p => (Sigma.mk i p.1, p.2)) <$> (H i).run saved)
    {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q source src a b)
    (input : A) (saved : S) :
    auditView <$> audit store control queryCost handler program (input, saved) =
      (simulateQ H (ExecutionProfile.run program input)).run saved := by
  induction program generalizing saved with
  | atomic code => rfl
  | query =>
      have h := handler.run_erase control queryCost (input, saved)
      rw [hhandler] at h
      have he := congrArg (Functor.map (fun p =>
        (ExecutionProfile.frame (Q := Q) src.position src.response input
          (p.1, { requests := [input] }), p.2))) h
      simpa only [audit, ExecutionProfile.run, auditView, auditFrame, Functor.map_map,
        simulateQ_map, simulateQ_spec_query, StateT.run_map, ExecutionProfile.frame] using he
  | seq initial following hi hf =>
      simp only [audit, ExecutionProfile.run, map_bind, map_pure, simulateQ_bind, StateT.run_bind,
        simulateQ_pure, StateT.run_pure, ← hi, bind_map_left]
      congr 1
      funext z
      simp only [auditView, ← hf, bind_pure_comp, Functor.map_map]
      rfl
  | branch left right hl hr =>
      cases input <;>
        simp only [audit, ExecutionProfile.run, simulateQ_map, StateT.run_map, ← hl, ← hr, Functor.map_map] <;> rfl
  | first retained body ih =>
      simp only [audit, ExecutionProfile.run, simulateQ_map, StateT.run_map, ← ih, Functor.map_map]
      rfl
  | loop body stop fuel hb hs =>
      exact auditLoop_source store control H _ _ _ _ _ _ hb hs fuel input saved
  | iterate counter body ih =>
      simp only [audit, ExecutionProfile.run, simulateQ_map, StateT.run_map]
      rw [← auditIteration_source store control H _ _ _ _ ih]
      simp only [Functor.map_map]
      rfl

/-- A profile on an actual instrumented native path is an execution profile of
the original code, even when the handler restricts or replays its replies. -/
theorem audit_mem_profile
    (hhandler : ∀ i saved, handler.denote (i, saved) =
      (fun p => (Sigma.mk i p.1, p.2)) <$> (H i).run saved)
    {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q source src a b)
    (input : A) (saved : S) (z : Audit I B S)
    (hz : z ∈ support (audit store control queryCost handler program (input, saved))) :
    (z.1.value.1, z.2) ∈ support (ExecutionProfile.run program input) := by
  apply support_simulateQ_run'_subset H (ExecutionProfile.run program input) saved
  change (z.1.value.1, z.2) ∈ support
    (Prod.fst <$> (simulateQ H (ExecutionProfile.run program input)).run saved)
  rw [← audit_source store control queryCost handler H hhandler, support_map, support_map]
  exact ⟨auditView z, ⟨z, hz, rfl⟩, rfl⟩

end Signatures.Runtime.BackendProgram.StateSimulation
