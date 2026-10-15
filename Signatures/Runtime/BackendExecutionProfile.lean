import Signatures.Runtime.BackendProgram

/-! Proof-only execution resources of original backend code. Profiles record
actual local work, visited control nodes, encoded boundary widths, loop counters
and chronological requests. They do not execute or price a transformed program.
In particular, zero-cost backend operations still count as executed nodes. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.ExecutionProfile

universe v w

structure Metrics (I : Type) where
  work : Nat := 0
  visits : Nat := 0
  width : Nat := 0
  counter : Nat := 0
  requests : List I := []

def Metrics.join {I : Type} (a b : Metrics I) : Metrics I where
  work := a.work + b.work
  visits := a.visits + b.visits
  width := max a.width b.width
  counter := max a.counter b.counter
  requests := a.requests ++ b.requests

/-- One executed control node, with all of its boundary values measured. -/
def Metrics.node {I : Type} (a : Metrics I) (width counter : Nat) : Metrics I :=
  { a with visits := a.visits + 1, width := max width a.width, counter := max counter a.counter }

def Metrics.Fits {I : Type} (a : Metrics I) (width counter : Nat) (allowed : I → Prop) : Prop :=
  a.width ≤ width ∧ a.counter ≤ counter ∧ ∀ i ∈ a.requests, allowed i

@[simp] theorem Metrics.fits_join {I : Type} (a b : Metrics I) (width counter : Nat)
    (allowed : I → Prop) :
    (a.join b).Fits width counter allowed ↔
      a.Fits width counter allowed ∧ b.Fits width counter allowed := by
  simp only [Fits, join, max_le_iff, List.mem_append, or_imp, forall_and]
  tauto

@[simp] theorem Metrics.fits_node {I : Type} (a : Metrics I) (w c width counter : Nat)
    (allowed : I → Prop) :
    (a.node w c).Fits width counter allowed ↔
      w ≤ width ∧ c ≤ counter ∧ a.Fits width counter allowed := by
  simp only [Fits, node, max_le_iff]
  tauto

abbrev Result (I A : Type) := A × Metrics I

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  {I : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}

def frame {A B : Type} (a : C.Str A) (b : C.Str B) (input : A)
    (result : Result I B) (extraWidth counter : Nat := 0) : Result I B :=
  (result.1, result.2.node (max extraWidth (max (Q.size a input) (Q.size b result.1))) counter)

def loop {A B : Type} (a : C.Str A) (b : C.Str B)
    (body : A → OracleComp spec (Result I (B ⊕ A)))
    (stop : A → OracleComp spec (Result I B)) : Nat → A → OracleComp spec (Result I B)
  | 0, input => (fun r => frame (Q := Q) a b input r 0 0) <$> stop input
  | fuel + 1, input => do
      let step ← body input
      match step.1 with
      | .inl result => pure (frame (Q := Q) a b input (result, step.2) 0 (fuel + 1))
      | .inr next => do
          let rest ← loop a b body stop fuel next
          pure (frame (Q := Q) a b input (rest.1, step.2.join rest.2) 0 (fuel + 1))

def iteration {A : Type} (a : C.Str A) (counter : C.Str Nat)
    (body : A → OracleComp spec (Result I A)) : Nat → A → OracleComp spec (Result I A)
  | 0, input => pure (frame (Q := Q) a a input (input, {}) (Q.size counter 0) 0)
  | count + 1, input => do
      let step ← body input
      let rest ← iteration a counter body count step.1
      pure (frame (Q := Q) a a input (rest.1, step.2.join rest.2)
        (Q.size counter (count + 1)) (count + 1))

def run {A B : Type} {a : C.Str A} {b : C.Str B} :
    Code Q spec iface a b → A → OracleComp spec (Result I B)
  | .atomic (f := f) code, input =>
      pure (frame (Q := Q) a b input (f input, { work := Q.cost code input }))
  | .query, input =>
      (fun reply => frame (Q := Q) iface.position iface.response input (⟨input, reply⟩, { requests := [input] })) <$>
        (liftM (spec.query input))
  | .seq initial following, input => do
      let first ← run initial input
      let second ← run following first.1
      pure (frame (Q := Q) a b input (second.1, first.2.join second.2))
  | .branch (a := leftRep) (b := rightRep) (d := output) left right, input =>
      (frame (Q := Q) (StepClass.HasSum.sum leftRep rightRep) output input ·) <$>
        (match input with | .inl x => run left x | .inr x => run right x)
  | .first (a := inputRep) (b := outputRep) saved body, input =>
      (fun r => frame (Q := Q) (StepClass.HasProd.prod inputRep saved)
        (StepClass.HasProd.prod outputRep saved) input ((r.1, input.2), r.2) (Q.size saved input.2)) <$>
        run body input.1
  | .loop (s := state) (b := output) body stop fuel, input =>
      loop (Q := Q) state output (run body) (run stop) fuel input
  | .iterate (s := state) counter body, input =>
      (frame (Q := Q) (StepClass.HasProd.prod counter state) state input ·) <$>
        iteration (Q := Q) state counter (run body) input.1 input.2

omit [C.HasProd] [C.HasSum] in
theorem loop_erase {A B : Type} (a : C.Str A) (b : C.Str B)
    (body : A → OracleComp spec (Result I (B ⊕ A)))
    (stop : A → OracleComp spec (Result I B)) (fuel : Nat) (input : A) :
    Prod.fst <$> loop (Q := Q) a b body stop fuel input =
      loopDenote (fun x => Prod.fst <$> body x) (fun x => Prod.fst <$> stop x) fuel input := by
  induction fuel generalizing input with
  | zero => simp [loop, loopDenote, frame, Functor.map_map]
  | succ fuel ih =>
      simp only [loop, loopDenote, map_bind, bind_map_left]
      congr 1
      funext p
      cases h : p.1 with
      | inl result => simp [frame]
      | inr next => simpa [h, frame, Functor.map_map] using ih next

omit [C.HasProd] [C.HasSum] in
theorem iteration_erase {A : Type} (a : C.Str A) (counter : C.Str Nat)
    (body : A → OracleComp spec (Result I A)) (count : Nat) (input : A) :
    Prod.fst <$> iteration (Q := Q) a counter body count input =
      repeatDenote (fun x => Prod.fst <$> body x) count input := by
  induction count generalizing input with
  | zero => simp [iteration, repeatDenote, frame]
  | succ count ih =>
      simp only [iteration, repeatDenote, map_bind, bind_map_left, map_pure]
      congr 1
      funext p
      simpa [frame] using ih p.1

theorem erase {A B : Type} {a : C.Str A} {b : C.Str B}
    (program : Code Q spec iface a b) (input : A) :
    Prod.fst <$> run program input = program.denote input := by
  induction program with
  | atomic code => simp [run, frame, Code.denote]
  | query => simp [run, frame, Code.denote, Functor.map_map]
  | seq initial following hi hf =>
      simp only [run, Code.denote, map_bind, map_pure, frame]
      simp only [bind_pure_comp]
      simp_rw [hf]
      rw [← hi, bind_map_left]
  | branch left right hl hr =>
      cases input with
      | inl value => simpa [run, Code.denote, frame, Functor.map_map] using hl value
      | inr value => simpa [run, Code.denote, frame, Functor.map_map] using hr value
  | first saved body ih =>
      simp only [run, Code.denote, Functor.map_map, frame]
      rw [← ih]
      simp only [Functor.map_map]
  | loop body stop fuel hb hs =>
      simp only [run, Code.denote, loop_erase]
      simp_rw [hb, hs]
  | iterate counter body ih =>
      simp only [run, Code.denote, Functor.map_map, frame]
      change Prod.fst <$> iteration _ _ _ _ _ = _
      rw [iteration_erase]
      simp_rw [ih]

/-- All resource limits concern the original program's executions. A symbolic
handler price can subsequently be substituted without assuming a transformed
program budget. `allowed` constrains only requests reached on these executions. -/
def Within {A B : Type} {a : C.Str A} {b : C.Str B} (program : Code Q spec iface a b)
    (input : A) (work visits queries width counter : Nat) (allowed : I → Prop) : Prop :=
  ∀ r ∈ support (run program input),
    r.2.work ≤ work ∧ r.2.visits ≤ visits ∧ r.2.requests.length ≤ queries ∧
      r.2.Fits width counter allowed

end Signatures.Runtime.BackendProgram.ExecutionProfile
