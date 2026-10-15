import Signatures.Runtime.BackendStateSimulationExecution

/-! Erasing the proof-only profile retains the actual costed native execution,
including every local call, retained frame, routing operation and loop test. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.StateSimulation

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QD : Q.IsDistributive]
  {I J S : Type} {source : OracleSpec I} {target : OracleSpec J}
  {src : Interface (C := C) source} {dst : Interface (C := C) target}
  (store : C.Str S) (control : ControlCosts)
  (queryCost : (j : J) → target.Range j → Nat)
  (handler : Code Q target dst (StepClass.HasProd.prod src.position store)
    (StepClass.HasProd.prod src.response store))

omit [Q.HasCategory] QP in
theorem auditLoop_erase {A B : Type} (a : C.Str A) (b : C.Str B)
    (body : A × S → OracleComp target (Audit I (B ⊕ A) S))
    (stop : A × S → OracleComp target (Audit I B S)) (fuel : Nat) (input : A × S) :
    Prod.fst <$> auditLoop (Q := Q) store control a b body stop fuel input =
      loopRun (fun n p => control.loop n (Q.size (StepClass.HasProd.prod a store) p))
        (fun p => (fun z => ⟨distributeValue z.value,
          z.steps + loopBodyWork (Q := Q) store control a b p z.value⟩) <$> (Prod.fst <$> body p))
        (fun p => Prod.fst <$> stop p) fuel input := by
  induction fuel generalizing input with
  | zero => simp [auditLoop, loopRun, auditFrame, chargeRun, Functor.map_map]
  | succ fuel ih =>
      simp only [auditLoop, loopRun, map_bind, bind_map_left]
      congr 1
      funext z
      cases h : z.1.value.1 with
      | inl result =>
          have hd : distributeValue z.1.value = Sum.inl (result, z.1.value.2) := by
            simp [distributeValue, h]
          rw [hd]
          simp [auditFrame, Nat.add_assoc]
      | inr next =>
          have hd : distributeValue z.1.value = Sum.inr (next, z.1.value.2) := by
            simp [distributeValue, h]
          rw [hd]
          simp only [auditFrame, map_bind, map_pure]
          rw [← ih]
          simp only [bind_pure_comp, Functor.map_map]
          congr 1
          funext r
          congr 1
          omega

omit QD [C.HasSum] [Q.HasCategory] QP in
theorem auditIteration_erase {A : Type} (a : C.Str A) (counter : C.Str Nat)
    (body : A × S → OracleComp target (Audit I A S)) (count : Nat) (input : A × S) :
    Prod.fst <$> auditIteration (Q := Q) store control a counter body count input =
      iterationRun (fun n p => control.loop n
        (Q.size (StepClass.HasProd.prod counter (StepClass.HasProd.prod a store)) (n, p)))
        (fun p => Prod.fst <$> body p) count input := by
  induction count generalizing input with
  | zero => rfl
  | succ count ih =>
      simp only [auditIteration, iterationRun, map_bind, bind_map_left, map_pure, auditFrame]
      congr 1
      funext z
      rw [← ih]
      simp only [bind_pure_comp, Functor.map_map]

theorem audit_erase {A B : Type} {a : C.Str A} {b : C.Str B}
    (program : Code Q source src a b) (input : A × S) :
    Prod.fst <$> audit store control queryCost handler program input =
      (compile store handler program).run control queryCost input := by
  induction program with
  | atomic code => simp [audit, auditFrame, compile, Code.run, localWork, retainRun]
  | query => simp [audit, auditFrame, compile, Functor.map_map]
  | seq initial following hi hf =>
      simp only [audit, compile, Code.run, sequenceRun, map_bind, map_pure, auditFrame]
      simp_rw [← hf]
      rw [← hi]
      simp only [bind_map_left]
  | branch left right hl hr =>
      rcases input with ⟨side, saved⟩
      cases side <;>
        simp only [audit, auditFrame, compile, Code.run, sequenceRun, chargeRun, branchWork,
          localWork, distributeValue, Sum.elim_inl, Sum.elim_inr, ← hl, ← hr,
          pure_bind, bind_pure_comp, Functor.map_map]
      all_goals congr 1; funext z; congr 1; omega
  | first retained body ih =>
      rcases input with ⟨⟨input, kept⟩, saved⟩
      simp only [audit, auditFrame, compile, Code.run, sequenceRun, retainRun, firstWork,
        localWork, ← ih, pure_bind, map_pure, bind_pure_comp, Functor.map_map]
      congr 1
      funext z
      congr 1
      omega
  | loop body stop fuel hb hs =>
      simp only [audit, auditLoop_erase, compile, Code.run]
      simp_rw [hs, hb]
      congr 1
      funext p
      simp only [sequenceRun, map_pure, bind_pure_comp, loopBodyWork, localWork,
        distributeValue, Nat.add_assoc]
  | @iterate A a counter body ih =>
      simp only [audit, Functor.map_map, auditFrame, compile, Code.run, sequenceRun, pure_bind]
      have hi := funext fun p => (ih p).symm
      rw [hi]
      have h := auditIteration_erase (Q := Q) store control a counter
        (audit store control queryCost handler body) input.1.1 (input.1.2, input.2)
      rw [← h]
      simp only [bind_pure_comp, Functor.map_map, iterationWork, localWork]
      congr 1
      funext z
      congr 1
      omega

end Signatures.Runtime.BackendProgram.StateSimulation
