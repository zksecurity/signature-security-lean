import Signatures.Runtime.Lookup
import Signatures.Runtime.Weakening

/-! Association-list lookup with a compiled comparison expression. This extends atomic-key
lookup to structured keys without adding an arbitrary comparison callback to the machine. -/

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  {key val : Ty Atom}

def lookupExprBody (eq : Expr Op [key, key] .bool) :
    Expr Op [.pair key val, .pair .bool val, key, val, .list (.pair key val)] (.pair .bool val) :=
  .branch (.fst (.var (.there .here))) (.var (.there .here))
    (.letE (.var (.there (.there .here)))
      (.letE (.fst (.var (.there .here)))
        (.branch (eq.weakenTail [.pair key val, .pair .bool val, key, val, .list (.pair key val)])
          (.pair (.bool true) (.snd (.var (.there (.there .here)))))
          (.var (.there (.there (.there .here)))))))

def lookupExpr (eq : Expr Op [key, key] .bool) :
    Expr Op [key, val, .list (.pair key val)] (.pair .bool val) :=
  .fold (.var (.there (.there .here))) (.pair (.bool false) (.var (.there .here)))
    (lookupExprBody eq)

theorem lookupExprBody_value (P : Primitives base Op) (eq : Expr Op [key, key] .bool)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y))
    (p : key.Value base × val.Value base) (acc : Bool × val.Value base)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    (lookupExprBody eq).denote P (p, acc, k, default, xs, ()) =
      if acc.1 = true then acc else if p.1 = k then (true, p.2) else acc := by
  have h := eq.weakenTail_denote
    (Δ := [.pair key val, .pair .bool val, key, val, .list (.pair key val)])
    P (p.1, k, ()) (p, acc, k, default, xs, ())
  simp only [Env.append] at h
  simp only [lookupExprBody, Expr.denote, Var.get, h, heq, decide_eq_true_eq]

theorem lookupExpr_value (P : Primitives base Op) (eq : Expr Op [key, key] .bool)
    [DecidableEq (key.Value base)]
    (heq : ∀ x y, eq.denote P (x, y, ()) = decide (x = y))
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((lookupExpr eq).run P (k, default, xs, ())).value = lookupValue k default xs := by
  rw [Expr.run_value]
  simp only [lookupExpr, Expr.denote, Var.get, lookupExprBody_value P eq heq]
  exact lookup_fold k default xs

theorem lookupExprBody_steps_le (P : Primitives base Op) (eq : Expr Op [key, key] .bool)
    (cEq : Nat) (heq : ∀ x y, (eq.run P (x, y, ())).steps ≤ cEq)
    (p : key.Value base × val.Value base) (acc : Bool × val.Value base)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((lookupExprBody eq).run P (p, acc, k, default, xs, ())).steps ≤ cEq + 19 := by
  have h := eq.weakenTail_run
    (Δ := [.pair key val, .pair .bool val, key, val, .list (.pair key val)])
    P (p.1, k, ()) (p, acc, k, default, xs, ())
  simp only [Env.append] at h
  have hb := heq p.1 k
  by_cases hf : acc.1 = true <;> by_cases hv : (eq.run P (p.1, k, ())).value = true <;>
    simp only [lookupExprBody, Expr.run, Var.get, Var.depth, h, hf, hv,
      Bool.false_eq_true, ite_true, ite_false] <;> omega

theorem lookupExpr_steps_le (P : Primitives base Op) (eq : Expr Op [key, key] .bool)
    (cEq : Nat) (heq : ∀ x y, (eq.run P (x, y, ())).steps ≤ cEq)
    (k : key.Value base) (default : val.Value base) (xs : List (key.Value base × val.Value base)) :
    ((lookupExpr eq).run P (k, default, xs, ())).steps ≤ xs.length * (cEq + 22) + 9 := by
  have h := foldRun_steps_le
    (fun p acc => (lookupExprBody eq).run P (p, acc, k, default, xs, ()))
    (cEq + 19) (fun p acc => lookupExprBody_steps_le P eq cEq heq p acc k default xs)
    xs (false, default)
  dsimp [lookupExpr, Expr.run, Var.get, Var.depth]
  nlinarith

end Signatures.Runtime
