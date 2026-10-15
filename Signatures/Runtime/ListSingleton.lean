import Signatures.Runtime.BackendReverseCost

/-! Executable singleton-list decoding using a constant-size accumulator.
The first flag starts true and becomes false after the first cell; copying its
old value into the second flag detects exactly one cell without a size counter.
The candidate is retained only as runtime data. -/

namespace Signatures.Runtime.ListSingleton

abbrev stateTy {Atom : Type} (cell : Ty Atom) : Ty Atom := .pair .bool (.pair .bool cell)

def step {A : Type} (x : A) (acc : Bool × Bool × A) : Bool × Bool × A :=
  (false, acc.1, x)

def value {A : Type} (default : A) (xs : List A) : Bool × A :=
  (xs.foldl (fun acc x => step x acc) (true, false, default)).2

private theorem invalid_fold {A : Type} (xs : List A) (default : A) :
    (xs.foldl (fun acc x => step x acc) (false, false, default)).1 = false ∧
      (xs.foldl (fun acc x => step x acc) (false, false, default)).2.1 = false := by
  induction xs generalizing default with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih => exact ih x

@[simp] theorem value_nil {A : Type} (default : A) : value default [] = (false, default) := rfl
@[simp] theorem value_singleton {A : Type} (default x : A) : value default [x] = (true, x) := rfl

theorem value_multiple {A : Type} (default x y : A) (xs : List A) :
    (value default (x :: y :: xs)).1 = false := (invalid_fold xs y).2

/-- An accepted candidate is exactly the sole input cell. -/
theorem valid_iff {A : Type} (default : A) (xs : List A) :
    (value default xs).1 = true ↔ xs = [(value default xs).2] := by
  cases xs with
  | nil => simp
  | cons x xs =>
      cases xs with
      | nil => simp
      | cons y xs => simp only [value_multiple, Bool.false_eq_true, List.cons.injEq, List.cons_ne_nil, and_false]

theorem value_property {A : Type} (valid : A → Prop) (default : A) (xs : List A)
    (hd : valid default) (hx : ∀ x ∈ xs, valid x) : valid (value default xs).2 := by
  have hfold (ys : List A) (hy : ∀ y ∈ ys, valid y) (acc : Bool × Bool × A)
      (ha : valid acc.2.2) : valid (ys.foldl (fun acc x => step x acc) acc).2.2 := by
    induction ys generalizing acc with
    | nil => exact ha
    | cons y ys ih => exact ih (fun z hz => hy z (by simp [hz])) (step y acc) (hy y (by simp))
  exact hfold xs hx (true, false, default) hd

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  {cell : Ty Atom}

def body {Γ : List (Ty Atom)} : Expr Op (cell :: stateTy cell :: Γ) (stateTy cell) :=
  .pair (.bool false) (.pair (.fst (.var (.there .here))) (.var .here))

def scan {Γ : List (Ty Atom)} : Expr Op (.list cell :: cell :: Γ) (.pair .bool cell) :=
  .snd (.fold (.var .here) (.pair (.bool true) (.pair (.bool false) (.var (.there .here)))) body)

theorem body_denote (P : Primitives base Op) {Γ : List (Ty Atom)}
    (x : cell.Value base) (acc : Bool × Bool × cell.Value base) (env : Env base Γ) :
    body.denote P (x, acc, env) = step x acc := rfl

theorem scan_denote (P : Primitives base Op) {Γ : List (Ty Atom)}
    (xs : List (cell.Value base)) (default : cell.Value base) (env : Env base Γ) :
    scan.denote P (xs, default, env) = value default xs := rfl

end Signatures.Runtime.ListSingleton
