import Signatures.Runtime.BackendExpressionSize
import Signatures.Runtime.Weakening

/-! Appending unused environment slots preserves the compiled expression's
description allowance. It does not claim that retaining larger frames is free
at execution time; native runtime costs still depend on encoded frame widths.
-/

namespace Signatures.Runtime.BackendProgram.Expression

variable {Atom : Type} {Op : Ty Atom → Ty Atom → Type}

theorem variableDescription_weakenTail (allowance : Nat) {Γ a} (v : Var (Atom := Atom) Γ a)
    (Δ : List (Ty Atom)) :
    variableDescription allowance (v.weakenTail Δ) = variableDescription allowance v := by
  induction v <;> simp_all [Var.weakenTail, variableDescription]

theorem descriptionBound_weakenTail (allowance : Nat)
    (primitiveSize : {a b : Ty Atom} → Op a b → Nat)
    {Γ a} (e : Expr Op Γ a) (Δ : List (Ty Atom)) :
    descriptionBound allowance primitiveSize (e.weakenTail Δ) = descriptionBound allowance primitiveSize e := by
  induction e <;> simp_all [Expr.weakenTail, descriptionBound, variableDescription_weakenTail]

end Signatures.Runtime.BackendProgram.Expression
