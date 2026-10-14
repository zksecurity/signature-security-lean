import Signatures.Runtime.BackendProgram

/-! Componentwise implementation contracts for the common execution backend.

`Backend` fixes actual target program data and execution. Its implementation laws
concern local code, external primitives, and generic control constructors. They
are independent of any adversary or signature reduction. Compilation constructs
target code recursively and derives its complete execution law; no implementation
or budget for the finished reduction is a premise.

An instantiation must justify these contracts in its chosen machine model. This
module does not assert that such an instantiation exists for every backend.
-/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  (Q : QuantitativeStepClass.{0, v, w} C)
  {I : Type} (spec : OracleSpec I) (iface : Interface (C := C) spec)
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)

structure Backend where
  Program : {A B : Type} → C.Str A → C.Str B → Type x
  execute : {A B : Type} → {a : C.Str A} → {b : C.Str B} →
    Program a b → A → OracleComp spec (Run B)
  atomic : {A B : Type} → {a : C.Str A} → {b : C.Str B} → {f : A → B} →
    Q.Realizer a b f → Program a b
  query : Program iface.position iface.response
  seq : {A B D : Type} → {a : C.Str A} → {b : C.Str B} → {d : C.Str D} →
    Program a b → Program b d → Program a d
  branch : {A B D : Type} → {a : C.Str A} → {b : C.Str B} → {d : C.Str D} →
    Program a d → Program b d → Program (StepClass.HasSum.sum a b) d
  first : {A B S : Type} → {a : C.Str A} → {b : C.Str B} →
    (s : C.Str S) → Program a b → Program (StepClass.HasProd.prod a s) (StepClass.HasProd.prod b s)
  loop : {S B : Type} → {s : C.Str S} → {b : C.Str B} →
    Program s (StepClass.HasSum.sum b s) → Program s b → Nat → Program s b
  iterate : {S : Type} → {s : C.Str S} → (counter : C.Str Nat) →
    Program s s → Program (StepClass.HasProd.prod counter s) s
  local_execute : ∀ {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f) (input : A),
    execute (atomic code) input = (Code.atomic code : Code Q spec iface a b).run control queryCost input
  query_execute : ∀ input,
    execute query input = (Code.query : Code Q spec iface iface.position iface.response).run
      control queryCost input
  seq_execute : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    (initial : Program a b) (following : Program b d) (input : A),
    execute (seq initial following) input =
      sequenceRun (fun value => control.sequence (Q.size a input) (Q.size b value))
        (execute initial input) (execute following)
  branch_execute : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    (left : Program a d) (right : Program b d) (input : A ⊕ B),
    execute (branch left right) input =
      chargeRun (control.branch (Q.size (StepClass.HasSum.sum a b) input))
        (match input with | .inl value => execute left value | .inr value => execute right value)
  first_execute : ∀ {A B S : Type} {a : C.Str A} {b : C.Str B}
    (saved : C.Str S) (body : Program a b) (input : A × S),
    execute (first saved body) input =
      retainRun (fun result => control.retain (Q.size saved input.2) (Q.size b result))
        input.2 (execute body input.1)
  loop_execute : ∀ {S B : Type} {s : C.Str S} {b : C.Str B}
    (body : Program s (StepClass.HasSum.sum b s)) (stop : Program s b) (fuel : Nat) (input : S),
    execute (loop body stop fuel) input =
      loopRun (fun count state => control.loop count (Q.size s state))
        (execute body) (execute stop) fuel input
  iterate_execute : ∀ {S : Type} {s : C.Str S} (counter : C.Str Nat)
    (body : Program s s) (input : Nat × S),
    execute (iterate counter body) input =
      iterationRun (fun count state => control.loop count
        (Q.size (StepClass.HasProd.prod counter s) (count, state)))
        (execute body) input.1 input.2

variable {Q spec iface control queryCost}

def Backend.compile (backend : Backend.{v, w, x} Q spec iface control queryCost)
    {A B : Type} {a : C.Str A} {b : C.Str B} : Code Q spec iface a b → backend.Program a b
  | .atomic code => backend.atomic code
  | .query => backend.query
  | .seq initial following => backend.seq (backend.compile initial) (backend.compile following)
  | .branch left right => backend.branch (backend.compile left) (backend.compile right)
  | .first saved body => backend.first saved (backend.compile body)
  | .loop body stop fuel => backend.loop (backend.compile body) (backend.compile stop) fuel
  | .iterate counter body => backend.iterate counter (backend.compile body)

/-- The complete costed execution is derived from component implementation laws. -/
theorem Backend.compile_execute (backend : Backend.{v, w, x} Q spec iface control queryCost)
    {A B : Type} {a : C.Str A} {b : C.Str B}
    (code : Code Q spec iface a b) (input : A) :
    backend.execute (backend.compile code) input = code.run control queryCost input := by
  induction code with
  | atomic code => exact backend.local_execute code input
  | query => exact backend.query_execute input
  | seq initial following hi hf =>
      simp only [compile, backend.seq_execute, Code.run, hi]
      congr 1
      funext value
      exact hf value
  | branch left right hl hr =>
      cases input <;> simp [compile, backend.branch_execute, Code.run, hl, hr]
  | first saved body ih => simp [compile, backend.first_execute, Code.run, ih]
  | loop body stop fuel hb hs =>
      simp only [compile, backend.loop_execute, Code.run]
      congr 1 <;> funext state
      · exact hb state
      · exact hs state
  | iterate counter body ih =>
      simp only [compile, backend.iterate_execute, Code.run]
      congr 1
      funext state
      exact ih state

theorem Backend.compile_erase (backend : Backend.{v, w, x} Q spec iface control queryCost)
    {A B : Type} {a : C.Str A} {b : C.Str B}
    (code : Code Q spec iface a b) (input : A) :
    Run.value <$> backend.execute (backend.compile code) input = code.denote input := by
  rw [backend.compile_execute, Code.run_erase]

/-- Transfer any derived all-path bound to the actual assembled program. The
bound is a property to prove about the finite assembly, not a backend axiom. -/
theorem Backend.compile_bound (backend : Backend.{v, w, x} Q spec iface control queryCost)
    {A B : Type} {a : C.Str A} {b : C.Str B}
    (code : Code Q spec iface a b) (input : A) (budget : Nat)
    (hbound : ∀ z ∈ support (code.run control queryCost input), z.steps ≤ budget)
    (z : Run B) (hz : z ∈ support (backend.execute (backend.compile code) input)) :
    z.steps ≤ budget := by
  rw [backend.compile_execute] at hz
  exact hbound z hz

/-- Description sizes and assembly expansion are properties of the selected
backend's actual program representation. They are fixed before selecting a
caller, and cannot be replaced by online-runtime bounds. -/
structure Backend.DescriptionBound (backend : Backend.{v, w, x} Q spec iface control queryCost)
    (sizes : DescriptionSize Q) (factor : Nat) where
  size : {A B : Type} → {a : C.Str A} → {b : C.Str B} → backend.Program a b → Nat
  atomic_le : ∀ {A B : Type} {a : C.Str A} {b : C.Str B} {f : A → B}
    (code : Q.Realizer a b f), size (backend.atomic code) ≤ factor * (sizes.localSize code + 1)
  query_le : size backend.query ≤ factor
  seq_le : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    (initial : backend.Program a b) (following : backend.Program b d),
    size (backend.seq initial following) ≤ size initial + size following + factor
  branch_le : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    (left : backend.Program a d) (right : backend.Program b d),
    size (backend.branch left right) ≤ size left + size right + factor
  first_le : ∀ {A B S : Type} {a : C.Str A} {b : C.Str B}
    (saved : C.Str S) (body : backend.Program a b),
    size (backend.first saved body) ≤ size body + factor
  loop_le : ∀ {S B : Type} {s : C.Str S} {b : C.Str B}
    (body : backend.Program s (StepClass.HasSum.sum b s)) (stop : backend.Program s b) (fuel : Nat),
    size (backend.loop body stop fuel) ≤ size body + size stop + factor * (fuel + 2)
  iterate_le : ∀ {S : Type} {s : C.Str S} (counter : C.Str Nat) (body : backend.Program s s),
    size (backend.iterate counter body) ≤ size body + factor

/-- Compiling control flow gives an explicit static-description bound. A loop
contains one body description, even when its iteration cap is large. -/
theorem Backend.compile_descriptionSize
    (backend : Backend.{v, w, x} Q spec iface control queryCost)
    (sizes : DescriptionSize Q) (factor : Nat) (description : backend.DescriptionBound sizes factor)
    {A B : Type} {a : C.Str A} {b : C.Str B} (code : Code Q spec iface a b) :
    description.size (backend.compile code) ≤ factor * code.descriptionSize sizes := by
  induction code with
  | atomic code => exact description.atomic_le code
  | query => simpa [compile, Code.descriptionSize] using description.query_le
  | seq initial following hi hf =>
      have h := description.seq_le (backend.compile initial) (backend.compile following)
      dsimp [compile, Code.descriptionSize]
      nlinarith
  | branch left right hl hr =>
      have h := description.branch_le (backend.compile left) (backend.compile right)
      dsimp [compile, Code.descriptionSize]
      nlinarith
  | first saved body ih =>
      have h := description.first_le saved (backend.compile body)
      dsimp [compile, Code.descriptionSize]
      nlinarith
  | loop body stop fuel hb hs =>
      have h := description.loop_le (backend.compile body) (backend.compile stop) fuel
      dsimp [compile, Code.descriptionSize]
      nlinarith
  | iterate counter body ih =>
      have h := description.iterate_le counter (backend.compile body)
      dsimp [compile, Code.descriptionSize]
      nlinarith

end Signatures.Runtime.BackendProgram
