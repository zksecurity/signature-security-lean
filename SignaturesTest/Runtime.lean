import Proofs.Runtime.Arithmetic
import Proofs.Runtime.Lookup
import Proofs.Runtime.Sampling
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Runtime-language regressions. No claim that the four security reductions have yet been
compiled into this backend: these guard the executable components needed for that work. -/

open Signatures.Runtime OracleComp OracleSpec

namespace SignaturesTest.Runtime

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private abbrev Base := cryptoBase F F F Bool Bool
private def primitives := arithmetic F F F Bool Bool PrimitiveCosts.unit

private def literal : Expr CryptoOp [] .nat := .nat 0
private def boundLiteral : Expr CryptoOp [] .nat := .letE (.nat 0) (.var .here)

-- Identical pure results do not imply identical runtimes; a local binding is not free.
example : (literal.run primitives ()).value = (boundLiteral.run primitives ()).value := rfl
example : (literal.run primitives ()).steps = 1 := rfl
example : (boundLiteral.run primitives ()).steps = 3 := rfl

private def entries : List (Bool × F) := [(false, 2), (true, 0), (true, 3)]

-- First match wins, even when its value is zero; absence has a separate flag.
example : ((lookup (val := scalar) CryptoOp.keyEq).run primitives (true, 4, entries, ())).value =
    (true, 0) := by decide
example : ((lookup (val := scalar) CryptoOp.keyEq).run primitives
    (true, 4, [(false, 2)], ())).value = (false, 4) := by decide
example : ((lookup (val := scalar) CryptoOp.keyEq).run primitives
    (true, 4, ([] : List (Bool × F)), ())).steps = 9 := rfl
example : ((lookup (val := scalar) CryptoOp.keyEq).run primitives
    (true, 4, entries, ())).steps ≤ 3 * (1 + 19) + 9 :=
  lookup_steps_le (val := scalar) primitives CryptoOp.keyEq 1 (by intros; rfl) true (4 : F) entries

private inductive Draw : Ty CryptoAtom → Ty CryptoAtom → Type
  | scalar : Draw .unit scalar

private def deterministic : Handler Base Draw unifSpec := fun cmd _ => match cmd with
  | .scalar => pure ⟨2, 7⟩

private noncomputable def uniform : Semantics Base Draw unifSpec := fun cmd _ => match cmd with
  | .scalar => $ᵗ F

-- The count is derived from the runtime interpreter, including allocation and reversal.
example : (sampleTable (Op := CryptoOp) Draw.scalar).run primitives deterministic (0, ()) =
    pure ⟨[], 10⟩ := by
  simp [sampleTable, sampleList, Program.run, Expr.run, Var.get, Var.depth, repeatRun, reverseList,
    foldRun]

example : (sampleTable (Op := CryptoOp) Draw.scalar).run primitives deterministic (3, ()) =
    pure ⟨[2, 2, 2], 82⟩ := by
  simp [sampleTable, sampleList, Program.run, Expr.run, Var.get, Var.depth, repeatRun, reverseList,
    foldRun, drawAndCons, deterministic]

example (n : Nat) :
    (sampleTable (Op := CryptoOp) Draw.scalar).denote primitives uniform (n, ()) =
      Vector.toList <$> SampleableType.vector F n :=
  sampleTable_uniform primitives uniform Draw.scalar rfl n

example (n : Nat) (z : Run (List F))
    (hz : z ∈ support ((sampleTable (Op := CryptoOp) Draw.scalar).run primitives deterministic (n, ()))) :
    z.steps ≤ n * 24 + 10 :=
  sampleTable_steps_le primitives deterministic Draw.scalar 7
    (by intro r hr; simp only [deterministic, support_pure, Set.mem_singleton_iff] at hr
        subst r; rfl) n z hz

end SignaturesTest.Runtime

open Lean Elab Command

-- Every runtime correctness/bound theorem must remain free of admissions or custom axioms.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Expr.run_value, ``Expr.steps_pos, ``Program.run_erase,
      ``Program.ret_steps_pos, ``repeatRun_steps_le, ``lookup_correct, ``lookup_steps_le,
      ``sampleList_length, ``sampleTable_steps_le, ``sampleTable_uniform] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
