import Signatures.Runtime.NaturalRange
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime NaturalRange

namespace SignaturesTest.NaturalRange

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev Base := cryptoBase (ZMod 3) (ZMod 3) (ZMod 3) Unit Unit
private def P := arithmetic (ZMod 3) (ZMod 3) (ZMod 3) Unit Unit PrimitiveCosts.unit

private abbrev checked {Γ : List (Ty CryptoAtom)} {t : Ty CryptoAtom} (w : Nat)
    (e : Expr CryptoOp Γ t) (env : Env Base Γ) := ExprBound PrimitiveCosts.unit w e env

private def discarded : Expr CryptoOp [.nat] .nat :=
  .letE (.op .natAdd (.pair (.var .here) (.var .here))) (.nat 0)

-- The final zero fits, but the discarded sum 126 still needs seven bits.
example : ¬ checked 6 discarded (63, ()) := by
  norm_num [checked, discarded, ExprBound, ValueBound, Expr.run, Var.get, arithmetic]
example : checked 7 discarded (63, ()) := by
  norm_num [checked, discarded, ExprBound, ValueBound, Expr.run, Var.get, arithmetic]

private def doubled : Expr CryptoOp [.nat] .nat :=
  .fold (.cons .unit (.cons .unit (.cons .unit .nil))) (.var .here)
    (.op .natAdd (.pair (.var (.there .here)) (.var (.there .here))))

-- Three actual accumulator transitions take 63 to 504, which needs nine bits.
example : ¬ checked 8 doubled (63, ()) := by
  norm_num [checked, doubled, ExprBound, ValueBound, foldChecks, Expr.run, Var.get, arithmetic]
example : checked 9 doubled (63, ()) := by
  norm_num [checked, doubled, ExprBound, ValueBound, foldChecks, Expr.run, Var.get, arithmetic]

example : checked (6 + (doubled.run P (63, ())).steps) doubled (63, ()) :=
  expr_trace_bound PrimitiveCosts.unit doubled 6 _ (63, ())
    (by norm_num [EnvBound, ValueBound]) le_rfl

-- A source branch not taken does not consume steps or produce intermediates.
example : checked 6 (.branch (.bool false) discarded (.nat 0)) (63, ()) := by
  norm_num [checked, ExprBound, Expr.run]

-- Fin values are bounded by their actual value, not the size of their type's modulus.
example : ValueBound (F := ZMod 3) (G₁ := ZMod 3) (G₂ := ZMod 3) (K := Unit) (M := Unit)
    (t := .list (.pair .nat (boundedNat 1000))) 6 [(12, ⟨63, by decide⟩)] := by
  norm_num [ValueBound]

#eval show IO Unit from do
  let r := doubled.run P (63, ())
  unless r.value == 504 do
    throw <| IO.userError "unexpected natural-range fold result"
  unless (discarded.run P (63, ())).value == 0 do
    throw <| IO.userError "unexpected discarded-sum result"

end SignaturesTest.NaturalRange

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``value_mono, ``op_bound, ``expr_bound, ``expr_trace_bound] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
