import Proofs.Runtime.BackendReverseCost

/-! Chronological append using two executable reversals and one cons. This is
used for Schnorr's received-basis and signing histories; reversing the stored
order would change the meaning of an adversary's coefficient positions. -/

namespace Signatures.Runtime.ListSnoc

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  {cell : Ty Atom} {Γ : List (Ty Atom)}

def withReversals
    (first : Expr Op (.list cell :: cell :: .list cell :: Γ) (.list cell))
    (second : Expr Op (.list cell :: .list cell :: .list cell :: cell :: .list cell :: Γ) (.list cell)) :
    Expr Op (cell :: .list cell :: Γ) (.list cell) :=
  .letE (.var (.there .here)) (.letE first
    (.letE (.cons (.var (.there (.there .here))) (.var .here)) second))

def expression : Expr Op (cell :: .list cell :: Γ) (.list cell) :=
  withReversals reverseList reverseList

theorem denote (P : Primitives base Op) (x : cell.Value base)
    (xs : List (cell.Value base)) (env : Env base Γ) :
    expression.denote P (x, xs, env) = xs ++ [x] := by
  dsimp only [expression, withReversals, Expr.denote, Var.get]
  rw [reverseList_denote, reverseList_denote, List.reverse_cons, List.reverse_reverse]

end Signatures.Runtime.ListSnoc
