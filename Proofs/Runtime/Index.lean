import Proofs.Runtime.Language
import Mathlib.Data.List.GetD

/-! Full-scan linked-list indexing. The remaining index and a found flag are explicit
fold state; values beyond the end use the supplied default. Even the suffix after a hit
is traversed and charged, so no array-access or early-stop assumption is hidden. -/

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type} {cell : Ty Atom}

def indexBody (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat) :
    Expr Op [cell, .pair .nat (.pair .bool cell), .nat, cell, .list cell]
      (.pair .nat (.pair .bool cell)) :=
  .branch (.fst (.snd (.var (.there .here)))) (.var (.there .here))
    (.branch (.op eq (.pair (.fst (.var (.there .here))) (.nat 0)))
      (.pair (.nat 0) (.pair (.bool true) (.var .here)))
      (.pair (.op sub (.pair (.fst (.var (.there .here))) (.nat 1)))
        (.snd (.var (.there .here)))))

def index (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat) :
    Expr Op [.nat, cell, .list cell] cell :=
  .snd (.snd (.fold (.var (.there (.there .here)))
    (.pair (.var .here) (.pair (.bool false) (.var (.there .here)))) (indexBody eq sub)))

def indexStep {α : Type} (state : Nat × Bool × α) (x : α) : Nat × Bool × α :=
  if state.2.1 then state
  else if state.1 = 0 then (0, true, x) else (state.1 - 1, false, state.2.2)

theorem indexStep_found {α : Type} (xs : List α) (n : Nat) (v : α) :
    xs.foldl indexStep (n, true, v) = (n, true, v) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [indexStep] using ih

theorem indexStep_value {α : Type} (xs : List α) (n : Nat) (default : α) :
    (xs.foldl indexStep (n, false, default)).2.2 = (xs[n]?).getD default := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp [indexStep, indexStep_found]
      | succ n => simpa [List.foldl_cons, indexStep] using ih n

theorem indexBody_denote (P : Primitives base Op)
    (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat)
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (hsub : ∀ x y, P.execute sub (x, y) = x - y)
    (x : cell.Value base) (state : Nat × Bool × cell.Value base)
    (n : Nat) (default : cell.Value base) (xs : List (cell.Value base)) :
    (indexBody eq sub).denote P (x, state, n, default, xs, ()) = indexStep state x := by
  rcases state with ⟨k, b, v⟩
  cases b <;> by_cases hk : k = 0 <;>
    simp [indexBody, Expr.denote, Var.get, indexStep, heq, hsub, hk]

theorem index_denote (P : Primitives base Op)
    (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat)
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (hsub : ∀ x y, P.execute sub (x, y) = x - y)
    (n : Nat) (default : cell.Value base) (xs : List (cell.Value base)) :
    (index eq sub).denote P (n, default, xs, ()) = (xs[n]?).getD default := by
  simp only [index, Expr.denote, Var.get]
  simp_rw [indexBody_denote P eq sub heq hsub]
  exact indexStep_value xs n default

theorem indexBody_steps_le (P : Primitives base Op)
    (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat) (c : Nat)
    (heq : ∀ x y, P.cost eq (x, y) ≤ c) (hsub : ∀ x y, P.cost sub (x, y) ≤ c)
    (x : cell.Value base) (state : Nat × Bool × cell.Value base)
    (n : Nat) (default : cell.Value base) (xs : List (cell.Value base)) :
    ((indexBody eq sub).run P (x, state, n, default, xs, ())).steps ≤ 2 * c + 23 := by
  rcases state with ⟨k, b, v⟩
  have he := heq k 0
  have hs := hsub k 1
  cases b <;> by_cases hb : P.execute eq (k, 0) = true <;>
    simp [indexBody, Expr.run, Var.get, Var.depth, hb] <;> omega

theorem index_steps_le (P : Primitives base Op)
    (eq : Op (.pair .nat .nat) .bool) (sub : Op (.pair .nat .nat) .nat) (c : Nat)
    (heq : ∀ x y, P.cost eq (x, y) ≤ c) (hsub : ∀ x y, P.cost sub (x, y) ≤ c)
    (n : Nat) (default : cell.Value base) (xs : List (cell.Value base)) :
    ((index eq sub).run P (n, default, xs, ())).steps ≤ xs.length * (2 * c + 26) + 13 := by
  have hb := foldRun_steps_le
    (fun x state => (indexBody eq sub).run P (x, state, n, default, xs, ())) (2 * c + 23)
    (fun x state => indexBody_steps_le P eq sub c heq hsub x state n default xs)
    xs (n, false, default)
  dsimp [index, Expr.run, Var.get, Var.depth]
  nlinarith

end Signatures.Runtime
