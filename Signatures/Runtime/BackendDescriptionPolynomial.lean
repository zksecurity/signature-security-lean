import Signatures.Runtime.BackendLanguageSize
import Signatures.Runtime.PolynomialResources

/-! Fixed expression and program descriptions preserve polynomial bounds on
their original primitives and effects. This concerns the reduction's syntax;
it imposes no syntax restriction on an external caller. -/

namespace Signatures.Runtime.BackendProgram

variable {Atom : Type} {Op Cmd : Ty Atom → Ty Atom → Type}

namespace Expression

theorem variableDescription_polynomial (allowance : Nat → Nat)
    (hAllowance : PolynomiallyBounded allowance) {Γ a} (v : Var (Atom := Atom) Γ a) :
    PolynomiallyBounded (fun n => variableDescription (allowance n) v) := by
  induction v with
  | here => exact hAllowance
  | there v ih => exact ih.add ((PolynomiallyBounded.const 2).mul hAllowance)

theorem descriptionBound_polynomial (allowance : Nat → Nat)
    (primitiveSize : Nat → {a b : Ty Atom} → Op a b → Nat)
    (hAllowance : PolynomiallyBounded allowance)
    (hPrimitive : ∀ {a b} (op : Op a b), PolynomiallyBounded (fun n => primitiveSize n op))
    {Γ a} (e : Expr Op Γ a) :
    PolynomiallyBounded (fun n => descriptionBound (allowance n) (primitiveSize n) e) := by
  induction e <;> dsimp only [descriptionBound]
  all_goals repeat' first
    | assumption
    | apply variableDescription_polynomial allowance hAllowance
    | apply hPrimitive
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

theorem argumentsDescription_polynomial (allowance : Nat → Nat)
    (primitiveSize : Nat → {a b : Ty Atom} → Op a b → Nat)
    (hAllowance : PolynomiallyBounded allowance)
    (hPrimitive : ∀ {a b} (op : Op a b), PolynomiallyBounded (fun n => primitiveSize n op))
    {Γ Δ} (args : Args Op Γ Δ) :
    PolynomiallyBounded (fun n => argumentsDescription (allowance n) (primitiveSize n) args) := by
  induction args with
  | nil => exact hAllowance
  | cons head tail ih =>
      exact ((descriptionBound_polynomial allowance primitiveSize hAllowance hPrimitive head).add ih).add hAllowance

end Expression

namespace Language

theorem descriptionBound_polynomial (allowance : Nat → Nat)
    (primitiveSize : Nat → {a b : Ty Atom} → Op a b → Nat)
    (effectSize : Nat → {a b : Ty Atom} → Cmd a b → Nat)
    (hAllowance : PolynomiallyBounded allowance)
    (hPrimitive : ∀ {a b} (op : Op a b), PolynomiallyBounded (fun n => primitiveSize n op))
    (hEffect : ∀ {a b} (cmd : Cmd a b), PolynomiallyBounded (fun n => effectSize n cmd))
    {Γ a} (program : Program Op Cmd Γ a) :
    PolynomiallyBounded (fun n => descriptionBound (allowance n) (primitiveSize n) (effectSize n) program) := by
  induction program <;> dsimp only [descriptionBound]
  all_goals repeat' first
    | assumption
    | apply Expression.descriptionBound_polynomial allowance primitiveSize hAllowance hPrimitive
    | apply Expression.argumentsDescription_polynomial allowance primitiveSize hAllowance hPrimitive
    | apply hEffect
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

end Language

end Signatures.Runtime.BackendProgram
