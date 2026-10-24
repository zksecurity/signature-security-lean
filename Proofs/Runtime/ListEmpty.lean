import Proofs.Runtime.BackendReverseCost

/-! Executable emptiness detection. The fold visits every incoming cell and
retains its context, so discarding a malformed request is still charged. -/

namespace Signatures.Runtime.ListEmpty

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
  {cell : Ty Atom} {Γ : List (Ty Atom)}

def scan : Expr Op (.list cell :: Γ) .bool :=
  .fold (.var .here) (.bool true) (.bool false)

private theorem fold_false {A : Type} (xs : List A) :
    xs.foldl (fun (_ : Bool) _ => false) false = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

theorem denote (P : Primitives base Op) (xs : List (cell.Value base)) (env : Env base Γ) :
    scan.denote P (xs, env) = xs.isEmpty := by
  change xs.foldl (fun (_ : Bool) _ => false) true = xs.isEmpty
  cases xs with
  | nil => rfl
  | cons x xs => exact fold_false xs

end Signatures.Runtime.ListEmpty
