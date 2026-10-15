import Signatures.Runtime.BackendStateSimulation
import Signatures.Runtime.BackendExecutionProfile

/-! Joint cost and source-profile instrumentation for the native state-passing
compiler. The auxiliary interpreter is proof-only: it couples each actual
compiled execution to the original code's local work and control/query trace.
No cost bound for the completed transformed program is assumed. -/

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

def localWork {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) (input : A) : Nat :=
  Q.cost code input + control.localCall (Q.size a input) (Q.size b (f input))

def distributeValue {A B T : Type} (p : (A ⊕ B) × T) : (A × T) ⊕ (B × T) :=
  Sum.elim (fun a => Sum.inl (a, p.2)) (fun b => Sum.inr (b, p.2)) p.1

def branchWork {A B : Type} (a : C.Str A) (b : C.Str B) (input : A ⊕ B) (saved : S) : Nat :=
  localWork control (QD.distribute a b store) (input, saved) +
    control.sequence (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum a b) store) (input, saved))
      (Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store))
        (distributeValue (input, saved))) +
    control.branch (Q.size (StepClass.HasSum.sum (StepClass.HasProd.prod a store)
      (StepClass.HasProd.prod b store)) (distributeValue (input, saved)))

def firstWork {A B T : Type} (a : C.Str A) (b : C.Str B) (retained : C.Str T)
    (input : A × T) (saved : S) (output : B × S) : Nat :=
  localWork control (shuffle (Q := Q) a retained store) (input, saved) +
    localWork control (shuffle (Q := Q) b store retained) (output, input.2) +
    control.retain (Q.size retained input.2) (Q.size (StepClass.HasProd.prod b store) output) +
    control.sequence (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod a store) retained)
      ((input.1, saved), input.2))
      (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod b store) retained) (output, input.2)) +
    control.sequence (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod a retained) store) (input, saved))
      (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod a store) retained) ((input.1, saved), input.2))

def loopBodyWork {A B : Type} (a : C.Str A) (b : C.Str B)
    (input : A × S) (output : (B ⊕ A) × S) : Nat :=
  localWork control (QD.distribute b a store) output +
    control.sequence (Q.size (StepClass.HasProd.prod a store) input)
      (Q.size (StepClass.HasProd.prod (StepClass.HasSum.sum b a) store) output)

def iterationWork {A : Type} (a : C.Str A) (counter : C.Str Nat)
    (input : (Nat × A) × S) : Nat :=
  localWork control (associate (Q := Q) counter a store) input +
    control.sequence (Q.size (StepClass.HasProd.prod (StepClass.HasProd.prod counter a) store) input)
      (Q.size (StepClass.HasProd.prod counter (StepClass.HasProd.prod a store))
        (input.1.1, (input.1.2, input.2)))

abbrev Audit (I B S : Type) := Run (B × S) × ExecutionProfile.Metrics I

def auditFrame {A B : Type} (a : C.Str A) (b : C.Str B) (input : A)
    (result : Run (B × S)) (metrics : ExecutionProfile.Metrics I)
    (extraWidth counter : Nat := 0) : Audit I B S :=
  (result, (ExecutionProfile.frame (Q := Q) a b input (result.value.1, metrics) extraWidth counter).2)

def auditLoop {A B : Type} (a : C.Str A) (b : C.Str B)
    (body : A × S → OracleComp target (Audit I (B ⊕ A) S))
    (stop : A × S → OracleComp target (Audit I B S)) :
    Nat → A × S → OracleComp target (Audit I B S)
  | 0, input => (fun z => auditFrame (Q := Q) a b input.1
      ⟨z.1.value, z.1.steps + control.loop 0 (Q.size (StepClass.HasProd.prod a store) input)⟩ z.2) <$>
        stop input
  | fuel + 1, input => do
      let z ← body input
      let fee := loopBodyWork (Q := Q) store control a b input z.1.value +
        control.loop (fuel + 1) (Q.size (StepClass.HasProd.prod a store) input)
      match z.1.value.1 with
      | .inl result => pure (auditFrame (Q := Q) a b input.1
          ⟨(result, z.1.value.2), z.1.steps + fee⟩ z.2 0 (fuel + 1))
      | .inr next => do
          let rest ← auditLoop a b body stop fuel (next, z.1.value.2)
          pure (auditFrame (Q := Q) a b input.1
            ⟨rest.1.value, z.1.steps + rest.1.steps + fee⟩ (z.2.join rest.2) 0 (fuel + 1))

def auditIteration {A : Type} (a : C.Str A) (counter : C.Str Nat)
    (body : A × S → OracleComp target (Audit I A S)) :
    Nat → A × S → OracleComp target (Audit I A S)
  | 0, input => pure (auditFrame (Q := Q) a a input.1
      ⟨input, control.loop 0 (Q.size (StepClass.HasProd.prod counter (StepClass.HasProd.prod a store)) (0, input))⟩
      {} (Q.size counter 0) 0)
  | count + 1, input => do
      let step ← body input
      let rest ← auditIteration a counter body count step.1.value
      pure (auditFrame (Q := Q) a a input.1
        ⟨rest.1.value, step.1.steps + rest.1.steps +
          control.loop (count + 1)
            (Q.size (StepClass.HasProd.prod counter (StepClass.HasProd.prod a store)) (count + 1, input))⟩
        (step.2.join rest.2) (Q.size counter (count + 1)) (count + 1))

def audit {A B : Type} {a : C.Str A} {b : C.Str B} : Code Q source src a b →
    A × S → OracleComp target (Audit I B S)
  | .atomic (f := f) code, input => pure (auditFrame (Q := Q) a b input.1
      ⟨(f input.1, input.2), localWork control code input.1 +
        control.retain (Q.size store input.2) (Q.size b (f input.1))⟩
      { work := Q.cost code input.1 })
  | .query, input => (fun z => auditFrame (Q := Q) src.position src.response input.1 z
      { requests := [input.1] }) <$> handler.run control queryCost input
  | .seq (b := middle) initial following, input => do
      let first ← audit initial input
      let second ← audit following first.1.value
      pure (auditFrame (Q := Q) a b input.1
        ⟨second.1.value, first.1.steps + second.1.steps +
          control.sequence (Q.size (StepClass.HasProd.prod a store) input)
            (Q.size (StepClass.HasProd.prod middle store) first.1.value)⟩ (first.2.join second.2))
  | .branch (a := leftRep) (b := rightRep) (d := output) left right, input =>
      (fun z => auditFrame (Q := Q) (StepClass.HasSum.sum leftRep rightRep) output input.1
        ⟨z.1.value, z.1.steps + branchWork (Q := Q) store control leftRep rightRep input.1 input.2⟩ z.2) <$>
          (match input.1 with | .inl x => audit left (x, input.2) | .inr x => audit right (x, input.2))
  | .first (a := inputRep) (b := outputRep) retained body, input =>
      (fun z => auditFrame (Q := Q) (StepClass.HasProd.prod inputRep retained)
        (StepClass.HasProd.prod outputRep retained) input.1
        ⟨((z.1.value.1, input.1.2), z.1.value.2), z.1.steps +
          firstWork (Q := Q) store control inputRep outputRep retained input.1 input.2 z.1.value⟩ z.2
        (Q.size retained input.1.2)) <$> audit body (input.1.1, input.2)
  | .loop (s := state) (b := output) body stop fuel, input =>
      auditLoop (Q := Q) store control state output (audit body) (audit stop) fuel input
  | .iterate (s := state) counter body, input =>
      (fun z => auditFrame (Q := Q) (StepClass.HasProd.prod counter state) state input.1
        ⟨z.1.value, z.1.steps + iterationWork (Q := Q) store control state counter input⟩ z.2) <$>
          auditIteration (Q := Q) store control state counter (audit body) input.1.1 (input.1.2, input.2)

end Signatures.Runtime.BackendProgram.StateSimulation
