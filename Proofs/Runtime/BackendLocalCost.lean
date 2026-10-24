import Proofs.Runtime.BackendExpression

/-! Local implementation-cost contracts for the expression compiler.

The overhead function receives encoded sizes of values touched by an operation.
It is fixed with the backend, and is not assumed constant or polynomial here.
Every law concerns a primitive or generic code constructor. In particular the
fold law charges the actual body code at every iteration; it is not a bound on
a complete expression or reduction supplied as a premise.
-/

open PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]

/-- Backend work for structural local code. The semantic functions in the laws
are indexed by their executable realizers, including the caller's own code. -/
structure LocalCostLaws (Q : QuantitativeStepClass.{0, v, w} C) [Q.HasCategory]
    [QP : Q.HasProd] [QS : Q.HasSum] (overhead : Nat → Nat) : Prop where
  identity : ∀ {A : Type} (a : C.Str A) (input : A),
    Q.cost (Q.identity a) input ≤ overhead (Q.size a input)
  compose : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : B → D} (left : Q.Realizer a b f) (right : Q.Realizer b d g) (input : A),
    Q.cost (Q.compose left right) input ≤ Q.cost left input + Q.cost right (f input) +
      overhead (Q.size a input + Q.size b (f input) + Q.size d (g (f input)))
  fst : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A × B),
    Q.cost (QP.fst a b) input ≤ overhead (Q.size (StepClass.HasProd.prod a b) input + Q.size a input.1)
  snd : ∀ {A B : Type} (a : C.Str A) (b : C.Str B) (input : A × B),
    Q.cost (QP.snd a b) input ≤ overhead (Q.size (StepClass.HasProd.prod a b) input + Q.size b input.2)
  pair : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → B} {g : A → D} (left : Q.Realizer a b f) (right : Q.Realizer a d g) (input : A),
    Q.cost (QP.pair left right) input ≤ Q.cost left input + Q.cost right input +
      overhead (Q.size a input + Q.size (StepClass.HasProd.prod b d) (f input, g input))
  elim : ∀ {A B D : Type} {a : C.Str A} {b : C.Str B} {d : C.Str D}
    {f : A → D} {g : B → D} (left : Q.Realizer a d f) (right : Q.Realizer b d g) (input : A ⊕ B),
    Q.cost (QS.elim left right) input ≤ Sum.elim (Q.cost left) (Q.cost right) input +
      overhead (Q.size (StepClass.HasSum.sum a b) input + Q.size d (Sum.elim f g input))

/-- Accumulate real body work and data/control overhead over a concrete list. -/
def foldWork {A B : Type} (step : A → B → B) (body : A → B → Nat)
    (fee : List A → B → Nat) : List A → B → Nat
  | [], acc => fee [] acc
  | x :: xs, acc => body x acc + foldWork step body fee xs (step x acc) + fee (x :: xs) acc

theorem foldWork_mono {A B : Type} (step : A → B → B) (body body' : A → B → Nat)
    (fee fee' : List A → B → Nat)
    (hb : ∀ x acc, body x acc ≤ body' x acc)
    (hf : ∀ xs acc, fee xs acc ≤ fee' xs acc) (xs : List A) (acc : B) :
    foldWork step body fee xs acc ≤ foldWork step body' fee' xs acc := by
  induction xs generalizing acc with
  | nil => exact hf [] acc
  | cons x xs ih =>
      have hx := hb x acc
      have ht := ih (step x acc)
      have hc := hf (x :: xs) acc
      dsimp [foldWork]
      omega

/-- A length cap and preserved accumulator invariant turn the accumulated fold
cost into a concrete linear bound. Only encountered list elements are counted. -/
theorem foldWork_bound {A B : Type} (step : A → B → B) (body : A → B → Nat)
    (fee : List A → B → Nat) (valid : A → Prop) (inv : B → Prop)
    (bodyTime tickTime cap : Nat)
    (hb : ∀ x, valid x → ∀ acc, inv acc → body x acc ≤ bodyTime ∧ inv (step x acc))
    (hf : ∀ xs, xs.length ≤ cap → (∀ x ∈ xs, valid x) → ∀ acc, inv acc → fee xs acc ≤ tickTime)
    (xs : List A) (hl : xs.length ≤ cap) (hx : ∀ x ∈ xs, valid x) (acc : B) (hi : inv acc) :
    foldWork step body fee xs acc ≤ xs.length * (bodyTime + tickTime) + tickTime := by
  induction xs generalizing acc with
  | nil => simpa [foldWork] using hf [] hl hx acc hi
  | cons x xs ih =>
      obtain ⟨hb', hinv⟩ := hb x (hx x (by simp)) acc hi
      have ht := ih (by simpa using (Nat.le_trans (Nat.le_succ xs.length) hl))
        (fun y hy => hx y (by simp [hy])) (step x acc) hinv
      have hc := hf (x :: xs) hl hx acc hi
      simp only [foldWork, List.length_cons]
      nlinarith

/-- The encoded fold frame and final accumulator both contribute to overhead.
These are mathematical bounds; evaluating a size bound is not an extra runtime
operation performed by the generated program. -/
def foldFee (overhead : Nat → Nat) (data : DataRepresentation C)
    {A B E : Type} (a : C.Str A) (b : C.Str B) (e : C.Str E)
    (step : A × (B × E) → B) (env : E) (xs : List A) (acc : B) : Nat :=
  overhead (Q.size (StepClass.HasProd.prod (data.list a) (StepClass.HasProd.prod b e)) (xs, acc, env) +
    Q.size b (xs.foldl (fun acc x => step (x, acc, env)) acc))

structure DataCostLaws (data : DataRepresentation C) (code : DataCode Q data)
    (overhead : Nat → Nat) : Prop where
  unit : ∀ {A : Type} (a : C.Str A) (input : A),
    Q.cost (code.unit a) input ≤ overhead (Q.size a input + Q.size data.unit ())
  bool : ∀ value input,
    Q.cost (code.bool value) input ≤ overhead (Q.size data.unit input + Q.size data.bool value)
  nat : ∀ value input,
    Q.cost (code.nat value) input ≤ overhead (Q.size data.unit input + Q.size data.nat value)
  nil : ∀ {A : Type} (a : C.Str A) input,
    Q.cost (code.nil a) input ≤ overhead (Q.size data.unit input + Q.size (data.list a) [])
  cons : ∀ {A : Type} (a : C.Str A) (input : A × List A),
    Q.cost (code.cons a) input ≤ overhead (Q.size (StepClass.HasProd.prod a (data.list a)) input +
      Q.size (data.list a) (input.1 :: input.2))
  select : ∀ {A : Type} (a : C.Str A) (input : Bool × A),
    Q.cost (code.select a) input ≤ overhead (Q.size (StepClass.HasProd.prod data.bool a) input +
      Q.size (StepClass.HasSum.sum a a) (if input.1 = true then Sum.inl input.2 else Sum.inr input.2))
  fold : ∀ {A B E : Type} (a : C.Str A) (b : C.Str B) (e : C.Str E)
    {step : A × (B × E) → B}
    (body : Q.Realizer (StepClass.HasProd.prod a (StepClass.HasProd.prod b e)) b step)
    (input : List A × (B × E)),
    Q.cost (code.fold a b e body) input ≤
      foldWork (fun x acc => step (x, acc, input.2.2))
        (fun x acc => Q.cost body (x, acc, input.2.2))
        (foldFee (Q := Q) overhead data a b e step input.2.2) input.1 input.2.1

end Signatures.Runtime.BackendProgram
