import Proofs.Runtime.HeapExpressionCost
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime HeapBits SharedHeap WeierstrassCurve

namespace SignaturesTest.HeapExpression

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def curve : Affine (ZMod 3) := ⟨0, 0, 0, 1, 1⟩
private def native := arithmetic (ZMod 3) (ZMod 3) (ZMod 3) Unit Unit PrimitiveCosts.unit
private def address (n : Nat) : Address := List.replicate n ()

#eval show IO Unit from do
  let roots := [address 0, address 5, address 2]
  let frame := frameBits roots
  for i in List.range 5 do
    let out := frameGet (address i) frame
    unless out.value == roots[i]? do
      throw <| IO.userError "bit-frame register lookup mismatch"
    unless out.steps ≤ (i+1)*(3*6+5) do
      throw <| IO.userError "bit-frame register lookup exceeded cost"
  let pushed := framePush (address 3) frame
  unless pushed.value == frameBits (address 3 :: roots) do
    throw <| IO.userError "bit-frame push changed register order"
  unless pushed.steps == 4*3+2*frame.length+6 do
    throw <| IO.userError "bit-frame push cost mismatch"
  unless (frameGet [] [true, true]).value.isNone do
    throw <| IO.userError "unterminated frame address was accepted"

private def sum : Expr CryptoOp [] .nat :=
  .fold (.cons (.nat 1) (.cons (.nat 2) (.cons (.nat 3) .nil))) (.nat 0)
    (.op .natAdd (.pair (.var .here) (.var (.there .here))))

private def nested : Expr CryptoOp [] .nat :=
  .letE (.nat 3) (.letE (.nat 5)
    (.op .natAdd (.pair (.var (.there .here)) (.var .here))))

private def checkNat (e : Expr CryptoOp [] .nat) (expected : Nat) : IO Unit := do
  let out := (HeapExpression.compile 4 3 curve curve e).run [] empty
  let some (root, store) := out.value | throw <| IO.userError "valid compiled expression failed"
  unless (read root store.memory).value == some (.word (natBits 4 expected)) do
    throw <| IO.userError "compiled expression's returned root has wrong bits"
  let source := e.run native ()
  unless source.value == expected do
    throw <| IO.userError "test's native source result mismatch"
  unless store.count.length ≤ source.steps do
    throw <| IO.userError "compiled expression allocated too many nodes"
  unless store.memory.length ≤ source.steps*(2*13+2*source.steps+4) do
    throw <| IO.userError "compiled expression exceeded proved heap-space bound"
  unless out.steps ≤ source.steps * HeapExpression.budget 4 source.steps e do
    throw <| IO.userError "compiled expression exceeded proved bit-step bound"

#eval show IO Unit from do
  checkNat (.nat 3) 3
  checkNat (.fst (.pair (.nat 2) (.nat 7))) 2
  checkNat (.snd (.pair (.nat 2) (.nat 7))) 7
  checkNat nested 8
  checkNat sum 6
  checkNat (.fold (.cons (.nat 1) (.cons (.nat 2) .nil)) (.nat 0)
    (.fold (.cons (.var .here) .nil) (.var (.there .here))
      (.op .natAdd (.pair (.var .here) (.var (.there .here)))))) 3
  checkNat (.fold (.nil : Expr CryptoOp [] (.list .nat)) (.nat 5) (.nat 999)) 5
  checkNat (.branch (.bool false) (.nat 1000) (.nat 7)) 7
  checkNat (.branch (.bool true) (.nat 4) (.nat 1000)) 4
  checkNat (.branch (.op .natLt (.pair (.nat 1) (.nat 2))) (.nat 3) (.nat 4)) 3
  checkNat (.branch (.op .scalarEq (.pair (.op .zero .unit) (.op .one .unit))) (.nat 1) (.nat 2)) 2
  checkNat (.op (.finVal 1000) (.op (.finOfNat 1000) (.nat 15))) 15
  checkNat (.op .natAdd (.pair (.nat 14) (.nat 1))) 15
  let out := (HeapExpression.compile 4 3 curve curve (Expr.unit : Expr CryptoOp [] .unit)).run [] empty
  let some (root, store) := out.value | throw <| IO.userError "unit compilation failed"
  unless (read root store.memory).value == some (.word []) do
    throw <| IO.userError "unit was not stored as an empty word"

private def treeType : Nat → Ty CryptoAtom
  | 0 => .nat
  | n+1 => .pair (treeType n) (treeType n)

private def tree : (n : Nat) → Expr CryptoOp [] (treeType n)
  | 0 => .nat 1
  | n+1 => .letE (tree n) (.pair (.var .here) (.var .here))

-- Source-level binding and variable lookup preserve sharing, not just manual alloc.
#eval show IO Unit from do
  let out := (HeapExpression.compile 4 3 curve curve (tree 30)).run [] empty
  let some (root, store) := out.value | throw <| IO.userError "shared source tree failed"
  unless store.count.length == 31 do
    throw <| IO.userError "source compiler expanded shared values"
  let some (.pair left right) := (read root store.memory).value |
    throw <| IO.userError "shared tree root is not a pair"
  unless left == right do
    throw <| IO.userError "source compiler duplicated a bound value"
  let source := ((tree 30).run native ()).steps
  unless out.steps ≤ source * HeapExpression.budget 4 source (tree 30) do
    throw <| IO.userError "shared source tree exceeded bit-step bound"

-- Raw malformed code inputs fail; cyclic lists cannot bypass the fuel guard.
#eval show IO Unit from do
  let bad : Store := ⟨address 1, tape [.cons [] []]⟩
  let code := HeapExpression.Code.fold (.var []) (.word (natBits 4 0)) (.var (address 1))
  unless (code.run (frameBits [[]]) bad).value.isNone do
    throw <| IO.userError "cyclic heap list escaped bounded fold traversal"
  unless ((HeapExpression.Code.var []).run [] empty).value.isNone do
    throw <| IO.userError "missing register was accepted"
  let unit := alloc empty (.word [])
  let code := HeapExpression.Code.branch (.var []) (.word [true]) (.word [false])
  unless (code.run (frameBits [unit.value.1]) unit.value.2).value.isNone do
    throw <| IO.userError "unit word was accepted as a branch selector"

private def H : AddSubgroup curve.Point := ⊥
private instance : Module (ZMod 3) H := EllipticCurveCircuit.subgroupModule curve H (by
  intro P
  have hp : P = 0 := Subtype.ext (by simpa [H] using P.property)
  simp [hp])

-- Concrete use of the budget-derived correctness theorem, with no per-op
-- overflow premise and no assumed result of the compiled interpreter.
example : HeapExpression.ResultSpec 4 13 (atomRep (r := 3) H H (id : BitVec 4 → BitVec 4) id)
    [] 4 (t := .nat) 3
    ((HeapExpression.compile 4 3 curve curve (Expr.nat 3 : Expr CryptoOp [] .nat)).run [] empty) := by
  exact HeapExpression.compile_spec_of_budget H H id id (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) Function.injective_id Function.injective_id
    PrimitiveCosts.unit (.nat 3) [] [] () empty empty_represents trivial .nil 0 trivial (by decide)

example : ((HeapExpression.compile 4 3 curve curve (Expr.nat 3 : Expr CryptoOp [] .nat)).run [] empty).steps ≤
    4 * HeapExpression.budget 4 4 (Expr.nat 3 : Expr CryptoOp [] .nat) := by
  exact (HeapExpression.compile_costed_of_budget (r := 3) (M := BitVec 4) (Γ := [])
    H H (id : BitVec 4 → BitVec 4) id
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Function.injective_id Function.injective_id PrimitiveCosts.unit (.nat 3)
    [] [] () empty empty_represents trivial .nil 0 trivial (by decide)).2

end SignaturesTest.HeapExpression

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``frameGet_value, ``frameGet_steps, ``framePush_value, ``framePush_steps,
      ``frameBits_length, ``project_value, ``project_steps, ``readBool_value, ``readBool_steps,
      ``EnvRep.append, ``EnvRep.get, ``wellFormed_lookup, ``Represents.list_length,
      ``Represents.pair_parts, ``HeapExpression.foldLoop_spec,
      ``HeapExpression.ResultSpec.memory_bound, ``HeapExpression.compile_spec,
      ``HeapExpression.compile_spec_of_budget, ``HeapExpression.tape_le_budget,
      ``HeapExpression.read_le_budget, ``HeapExpression.alloc_le_budget,
      ``HeapExpression.framePush_le_budget, ``HeapExpression.primitive_le_budget,
      ``HeapExpression.bind_steps_spec, ``HeapExpression.foldLoop_steps,
      ``HeapExpression.compile_steps, ``HeapExpression.compile_costed_of_budget] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
