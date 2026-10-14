import Signatures.Runtime.Program
import PolyFun.Realizability.Quantitative.Closure

/-! Finite effectful programs over one quantitative backend.

Local functions carry actual backend code. Sequencing and branching are finite
syntax: neither constructor accepts a host-language continuation. A bounded loop
stores its body once. This is the assembly language for combining a general
caller with an implemented oracle handler.

The denotation is deliberately separate from backend implementation/cost laws.
In particular, this module does not assign unit cost to copying encoded values
or infer a conventional-machine runtime from this syntax alone.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  (Q : QuantitativeStepClass.{0, v, w} C)
  {I : Type} (spec : OracleSpec I)

/-- Pinned encodings for the remaining external effects. A query returns its
position together with its dependent reply, so caller updates can validate it. -/
structure Interface where
  position : C.Str I
  response : C.Str (Σ i, spec.Range i)

variable (iface : Interface (C := C) spec)

inductive Code : {A B : Type} → C.Str A → C.Str B → Type (max 1 v w)
  | atomic {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
      (code : Q.Realizer a b f) : Code a b
  | query : Code iface.position iface.response
  | seq {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
      (first : Code a b) (second : Code b d) : Code a d
  | branch {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
      (left : Code a d) (right : Code b d) : Code (StepClass.HasSum.sum a b) d
  | first {A B S : Type} {a : C.Str A} {b : C.Str B} (s : C.Str S)
      (body : Code a b) : Code (StepClass.HasProd.prod a s) (StepClass.HasProd.prod b s)
  | loop {S B : Type} {s : C.Str S} {b : C.Str B}
      (body : Code s (StepClass.HasSum.sum b s)) (stop : Code s b)
      (fuel : Nat) : Code s b
  | iterate {S : Type} {s : C.Str S} (counter : C.Str Nat)
      (body : Code s s) : Code (StepClass.HasProd.prod counter s) s

variable {Q spec iface}

/-- Fuel limits loop iterations; the final stop program is still executed.
This makes an exhausted caller distinguishable from a returned result. -/
def loopDenote {m : Type → Type} [Monad m] {S B : Type}
    (body : S → m (B ⊕ S)) (stop : S → m B) : Nat → S → m B
  | 0, state => stop state
  | fuel + 1, state => do
      match ← body state with
      | .inl result => pure result
      | .inr next => loopDenote body stop fuel next

def Code.denote {A B : Type} {a : C.Str A} {b : C.Str B} :
    Code Q spec iface a b → A → OracleComp spec B
  | .atomic (f := f) _, input => pure (f input)
  | .query, input => (fun reply => Sigma.mk input reply) <$> (liftM (spec.query input))
  | .seq initial following, input => initial.denote input >>= following.denote
  | .branch left right, input => match input with
      | .inl value => left.denote value
      | .inr value => right.denote value
  | .first _ body, input => (fun result => (result, input.2)) <$> body.denote input.1
  | .loop body stop fuel, input => loopDenote body.denote stop.denote fuel input
  | .iterate _ body, input => repeatDenote body.denote input.1 input.2

/-- Structural work is priced in encoded sizes. These functions are supplied
with the backend's implementation laws, not inferred to be constant-time. -/
structure ControlCosts where
  localCall : Nat → Nat → Nat
  query : Nat → Nat → Nat
  sequence : Nat → Nat → Nat
  branch : Nat → Nat
  retain : Nat → Nat → Nat
  loop : Nat → Nat → Nat

def sequenceRun {m : Type → Type} [Monad m] {A B : Type}
    (fee : A → Nat) (initial : m (Run A)) (following : A → m (Run B)) : m (Run B) := do
  let x ← initial
  let y ← following x.value
  pure ⟨y.value, x.steps + y.steps + fee x.value⟩

def chargeRun {m : Type → Type} [Functor m] {A : Type} (fee : Nat)
    (computation : m (Run A)) : m (Run A) :=
  (fun r => ⟨r.value, r.steps + fee⟩) <$> computation

def retainRun {m : Type → Type} [Functor m] {A S : Type}
    (fee : A → Nat) (saved : S) (computation : m (Run A)) : m (Run (A × S)) :=
  (fun r => ⟨(r.value, saved), r.steps + fee r.value⟩) <$> computation

def loopRun {m : Type → Type} [Monad m] {S B : Type}
    (fee : Nat → S → Nat) (body : S → m (Run (B ⊕ S))) (stop : S → m (Run B)) :
    Nat → S → m (Run B)
  | 0, state => chargeRun (fee 0 state) (stop state)
  | fuel + 1, state => do
      let step ← body state
      match step.value with
      | .inl result => pure ⟨result, step.steps + fee (fuel + 1) state⟩
      | .inr next => do
          let rest ← loopRun fee body stop fuel next
          pure ⟨rest.value, step.steps + rest.steps + fee (fuel + 1) state⟩

/-- Input-bounded iteration retains one body description. Every test/decrement
is charged, including the final zero test. -/
def iterationRun {m : Type → Type} [Monad m] {S : Type}
    (fee : Nat → S → Nat) (body : S → m (Run S)) : Nat → S → m (Run S)
  | 0, state => pure ⟨state, fee 0 state⟩
  | count + 1, state => do
      let step ← body state
      let rest ← iterationRun fee body count step.value
      pure ⟨rest.value, step.steps + rest.steps + fee (count + 1) state⟩

def Code.run (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
    {A B : Type} {a : C.Str A} {b : C.Str B} :
    Code Q spec iface a b → A → OracleComp spec (Run B)
  | .atomic (f := f) code, input =>
      pure ⟨f input, Q.cost code input + control.localCall (Q.size a input) (Q.size b (f input))⟩
  | .query, input =>
      (fun reply => ⟨⟨input, reply⟩, queryCost input reply +
        control.query (Q.size iface.position input) (Q.size iface.response ⟨input, reply⟩)⟩) <$>
          (liftM (spec.query input))
  | .seq (b := middle) initial following, input =>
      sequenceRun (fun value => control.sequence (Q.size a input) (Q.size middle value))
        (initial.run control queryCost input) (following.run control queryCost)
  | .branch (a := leftRep) (b := rightRep) left right, input =>
      chargeRun (control.branch (Q.size (StepClass.HasSum.sum leftRep rightRep) input))
      (match input with
       | .inl value => left.run control queryCost value
       | .inr value => right.run control queryCost value)
  | .first (b := resultRep) saved body, input =>
      retainRun (fun result => control.retain (Q.size saved input.2) (Q.size resultRep result))
        input.2 (body.run control queryCost input.1)
  | .loop body stop fuel, input =>
      loopRun (fun count state => control.loop count (Q.size a state))
        (body.run control queryCost) (stop.run control queryCost) fuel input
  | .iterate (s := stateRep) counter body, input =>
      iterationRun (fun count state => control.loop count
        (Q.size (StepClass.HasProd.prod counter stateRep) (count, state)))
        (body.run control queryCost) input.1 input.2

theorem iterationRun_erase {m : Type → Type} [Monad m] [LawfulMonad m] {S : Type}
    (fee : Nat → S → Nat) (body : S → m (Run S)) (count : Nat) (state : S) :
    Run.value <$> iterationRun fee body count state =
      repeatDenote (fun s => Run.value <$> body s) count state := by
  induction count generalizing state with
  | zero => simp [iterationRun, repeatDenote]
  | succ count ih =>
      simp [iterationRun, repeatDenote, map_bind, bind_map_left, ← ih]

theorem loopRun_erase {m : Type → Type} [Monad m] [LawfulMonad m] {S B : Type}
    (fee : Nat → S → Nat) (body : S → m (Run (B ⊕ S))) (stop : S → m (Run B))
    (fuel : Nat) (state : S) :
    Run.value <$> loopRun fee body stop fuel state =
      loopDenote (fun s => Run.value <$> body s) (fun s => Run.value <$> stop s) fuel state := by
  induction fuel generalizing state with
  | zero => simp [loopRun, loopDenote, chargeRun]
  | succ fuel ih =>
      simp only [loopRun, loopDenote, map_bind, bind_map_left]
      congr 1
      funext step
      cases hv : step.value with
      | inl result => simp
      | inr next => simpa [hv, map_bind] using ih next

theorem Code.run_erase (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
    {A B : Type} {a : C.Str A} {b : C.Str B}
    (code : Code Q spec iface a b) (input : A) :
    Run.value <$> code.run control queryCost input = code.denote input := by
  induction code with
  | atomic => simp [run, denote]
  | query => simp [run, denote]
  | seq initial following hi hf =>
      simp only [run, denote, sequenceRun, map_bind, bind_pure_comp, Functor.map_map]
      simp_rw [hf]
      rw [← hi, bind_map_left]
  | branch left right hl hr =>
      cases input <;> simp [run, denote, chargeRun, ← hl, ← hr]
  | first saved body ih =>
      simp [run, denote, retainRun, ← ih]
  | loop body stop fuel hb hs =>
      simp only [run, denote, loopRun_erase]
      simp_rw [hb, hs]
  | iterate counter body ih =>
      simp only [run, denote, iterationRun_erase]
      simp_rw [ih]

/-- Transfer a concrete execution path to the semantic support without
unfolding the compiled program's local code. -/
theorem Code.value_mem_denote (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
    {A B : Type} {a : C.Str A} {b : C.Str B}
    (code : Code Q spec iface a b) (input : A) (z : Run B)
    (hz : z ∈ support (code.run control queryCost input)) :
    z.value ∈ support (code.denote input) := by
  rw [← code.run_erase control queryCost input, support_map]
  exact ⟨z, hz, rfl⟩

/-- Static code accounting relative to actual local realizer descriptions.
The loop counter uses a conservative unary description bound. Its body and stop
code are each counted once, regardless of the number of iterations. -/
structure DescriptionSize (Q : QuantitativeStepClass.{0, v, w} C) where
  localSize : {A B : Type} → {a : C.Str A} → {b : C.Str B} → {f : A → B} →
    Q.Realizer a b f → Nat

def Code.descriptionSize (sizes : DescriptionSize Q)
    {A B : Type} {a : C.Str A} {b : C.Str B} : Code Q spec iface a b → Nat
  | .atomic code => sizes.localSize code + 1
  | .query => 1
  | .seq initial following => initial.descriptionSize sizes + following.descriptionSize sizes + 1
  | .branch left right => left.descriptionSize sizes + right.descriptionSize sizes + 1
  | .first _ body => body.descriptionSize sizes + 1
  | .loop body stop fuel => body.descriptionSize sizes + stop.descriptionSize sizes + fuel + 2
  | .iterate _ body => body.descriptionSize sizes + 1

theorem Code.loop_descriptionSize (sizes : DescriptionSize Q)
    {S B : Type} {s : C.Str S} {b : C.Str B}
    (body : Code Q spec iface s (StepClass.HasSum.sum b s))
    (stop : Code Q spec iface s b) (fuel : Nat) :
    (Code.loop body stop fuel).descriptionSize sizes =
      body.descriptionSize sizes + stop.descriptionSize sizes + fuel + 2 := rfl

end Signatures.Runtime.BackendProgram
