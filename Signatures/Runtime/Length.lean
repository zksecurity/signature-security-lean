import Signatures.Runtime.Language

/-! Executable list length, using the existing fold and natural increment.
It is ordinary local code, not a host-language length operation. -/

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}

def listLength {cell : Ty Atom} {Γ : List (Ty Atom)} (add : Op (.pair .nat .nat) .nat) :
    Expr Op (.list cell :: Γ) .nat :=
  .fold (.var .here) (.nat 0) (.op add (.pair (.var (.there .here)) (.nat 1)))

theorem fold_count {A : Type} (xs : List A) (n : Nat) :
    xs.foldl (fun acc _ => acc + 1) n = n + xs.length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, Nat.add_comm, Nat.add_left_comm]

theorem listLength_denote {cell : Ty Atom} {Γ : List (Ty Atom)}
    (P : Primitives base Op) (add : Op (.pair .nat .nat) .nat)
    (ha : ∀ x y, P.execute add (x, y) = x + y) (xs : List (cell.Value base)) (env : Env base Γ) :
    (listLength add).denote P (xs, env) = xs.length := by
  simp only [listLength, Expr.denote, Var.get, ha, fold_count, Nat.zero_add]

end Signatures.Runtime
