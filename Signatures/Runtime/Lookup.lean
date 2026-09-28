import Signatures.Runtime.Language

/-! A compiled association-list lookup. This is executable syntax in the runtime language;
key comparison is the only primitive instruction. Storage reads and loop control are charged
by the interpreter. The full scan is conservative but avoids any random-access assumption. -/

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  {key val : Ty Atom}

def lookupBody (eq : Op (.pair key key) .bool) :
    Expr Op [.pair key val, .pair .bool val, key, val, .list (.pair key val)] (.pair .bool val) :=
  .branch (.fst (.var (.there .here))) (.var (.there .here))
    (.branch (.op eq (.pair (.fst (.var .here)) (.var (.there (.there .here)))))
      (.pair (.bool true) (.snd (.var .here))) (.var (.there .here)))

/-- Inputs are the sought key, the default result, and an association list. Output includes
the presence flag, so a cached zero is never confused with a missing entry. -/
def lookup (eq : Op (.pair key key) .bool) :
    Expr Op [key, val, .list (.pair key val)] (.pair .bool val) :=
  .fold (.var (.there (.there .here))) (.pair (.bool false) (.var (.there .here)))
    (lookupBody eq)

def lookupValue {K V : Type} [DecidableEq K] (k : K) (default : V) : List (K × V) → Bool × V
  | [] => (false, default)
  | (k', v) :: xs => if k' = k then (true, v) else lookupValue k default xs

private theorem lookup_fold_found {K V : Type} [DecidableEq K] (k : K) (v : V)
    (xs : List (K × V)) :
    xs.foldl (fun acc p => if acc.1 = true then acc else
      if p.1 = k then (true, p.2) else acc) (true, v) = (true, v) := by
  induction xs with
  | nil => rfl
  | cons p xs ih => simpa using ih

theorem lookup_fold {K V : Type} [DecidableEq K] (k : K) (default : V)
    (xs : List (K × V)) :
    xs.foldl (fun acc p => if acc.1 = true then acc else
      if p.1 = k then (true, p.2) else acc) (false, default) = lookupValue k default xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
      by_cases h : p.1 = k
      · simp [lookupValue, h, lookup_fold_found]
      · simpa [lookupValue, h] using ih

theorem lookup_correct (P : Primitives base Op) (eq : Op (.pair key key) .bool)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, P.execute eq (x, y) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((lookup eq).run P (k, default, xs, ())).value = lookupValue k default xs := by
  rw [Expr.run_value]
  simpa [lookup, lookupBody, Expr.denote, Var.get, heq] using lookup_fold k default xs

theorem lookupBody_steps_le (P : Primitives base Op) (eq : Op (.pair key key) .bool)
    (cEq : Nat) (heq : ∀ x y, P.cost eq (x, y) ≤ cEq)
    (p : key.Value base × val.Value base) (acc : Bool × val.Value base)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((lookupBody eq).run P (p, acc, k, default, xs, ())).steps ≤ cEq + 16 := by
  have h := heq p.1 k
  by_cases hf : acc.1 = true <;> by_cases he : P.execute eq (p.1, k) = true <;>
    simp [lookupBody, Expr.run, Var.get, Var.depth, hf, he] <;> omega

theorem lookup_steps_le (P : Primitives base Op) (eq : Op (.pair key key) .bool)
    (cEq : Nat) (heq : ∀ x y, P.cost eq (x, y) ≤ cEq)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((lookup eq).run P (k, default, xs, ())).steps ≤ xs.length * (cEq + 19) + 9 := by
  have h := foldRun_steps_le
    (fun p acc => (lookupBody eq).run P (p, acc, k, default, xs, ()))
    (cEq + 16) (fun p acc => lookupBody_steps_le P eq cEq heq p acc k default xs)
    xs (false, default)
  dsimp [lookup, Expr.run, Var.get, Var.depth]
  nlinarith

end Signatures.Runtime
