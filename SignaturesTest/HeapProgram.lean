import Signatures.Runtime.HeapProgram
import Signatures.Runtime.HeapLoopRefinement
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime HeapBits SharedHeap WeierstrassCurve

namespace SignaturesTest.HeapProgram

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def curve : Affine (ZMod 3) := ⟨0, 0, 0, 1, 1⟩
private def native := arithmetic (ZMod 3) (ZMod 3) (ZMod 3) Unit Unit PrimitiveCosts.unit

#eval show IO Unit from do
  for w in List.range 9 do
    for n in List.range (2^w) do
      let bits := natBits w n
      let next := HeapLoop.tick bits
      unless next.steps == 2*w+1 do
        throw <| IO.userError "binary decrement cost mismatch"
      if n == 0 then
        unless next.value.isNone do
          throw <| IO.userError "zero counter was decremented"
      else
        unless next.value == some (natBits w (n-1)) do
          throw <| IO.userError "binary predecessor or width mismatch"

private def args : Args CryptoOp [] [.nat, .nat, .bool] :=
  .cons (.nat 2) (.cons (.op .natAdd (.pair (.nat 3) (.nat 4))) (.cons (.bool true) .nil))

#eval show IO Unit from do
  let actual := HeapArguments.run (HeapArguments.compile 4 3 curve curve args) [] empty
  let some (frame, heap) := actual.value | throw <| IO.userError "argument compilation failed"
  let expected := [natBits 4 2, natBits 4 7, [true]]
  for i in List.range 3 do
    let some root := (frameGet (List.replicate i ()) frame).value |
      throw <| IO.userError "callee frame has missing argument"
    unless (readWord heap.memory root).value == expected[i]? do
      throw <| IO.userError "callee argument order/value mismatch"
  let source := (args.run native ()).steps
  unless heap.count.length ≤ source do
    throw <| IO.userError "argument allocation exceeded source budget"
  unless actual.steps ≤ source * HeapArguments.budget 4 source args do
    throw <| IO.userError "argument frame construction exceeded bit budget"
  let bad := HeapArguments.run [.var []] [] empty
  unless bad.value.isNone do
    throw <| IO.userError "argument compiler accepted a missing caller register"

private inductive Cmd : Ty CryptoAtom → Ty CryptoAtom → Type
  | mark : Cmd .nat .nat

private def increment : Expr CryptoOp [.nat] .nat :=
  .op .natAdd (.pair (.var .here) (.nat 1))

-- Test-only handlers record queries so adaptive paths can be compared. These
-- logs are not claimed to be part of the certified production handler backend.
private def semanticHandler : HandlerM (cryptoBase (ZMod 3) (ZMod 3) (ZMod 3) Unit Unit)
    Cmd (StateM (List Nat))
  | _, _, .mark, n => do
    modify (fun log => log ++ [n])
    pure ⟨n+1, 1⟩

private def bitHandler : HeapProgram.HandlerM Cmd (StateM (List (List Bool)))
  | _, _, .mark, root, store => do
    let arg := readWord store.memory root
    match arg.value with
    | none => pure ⟨none, arg.steps+1⟩
    | some bits =>
      modify (fun log => log ++ [bits])
      let frame := framePush root []
      let out := (HeapExpression.compile 4 3 curve curve increment).run frame.value store
      pure ⟨out.value, arg.steps+frame.steps+out.steps+1⟩

private def check (code : Program CryptoOp Cmd [] .nat) (expected : Nat) (log : List Nat) : IO Unit := do
  let source := (code.run native semanticHandler ()).run []
  unless source.1.value == expected && source.2 == log do
    throw <| IO.userError "source program test expectations are wrong"
  let actual := ((HeapProgram.compile 4 3 curve curve code).run bitHandler [] empty).run []
  let some (root, heap) := actual.1.value | throw <| IO.userError "compiled program failed"
  unless (readWord heap.memory root).value == some (natBits 4 expected) do
    throw <| IO.userError "compiled program result differs from source"
  unless actual.2 == log.map (natBits 4) do
    throw <| IO.userError "compiled adaptive query log differs from source"

private def adaptive : Program CryptoOp Cmd [] .nat :=
  .bind (.query .mark (.nat 2))
    (.branch (.op .natLt (.pair (.var .here) (.nat 4)))
      (.query .mark (.op .natAdd (.pair (.var .here) (.nat 4))))
      (.query .mark (.nat 12)))

private def call : Program CryptoOp Cmd [] .nat :=
  .bind (.ret (.nat 9))
    (.call (.ret (.op .natAdd (.pair (.var .here) (.var (.there .here)))))
      (.cons (.nat 2) (.cons (.var .here) .nil)))

#eval show IO Unit from do
  check (.ret (.nat 7)) 7 []
  check adaptive 8 [2, 7]
  check call 11 []
  check (.branch (.bool false) (.query .mark (.nat 2)) (.ret (.nat 3))) 3 []
  check (.loop (.nat 3) (.nat 1) (.query .mark (.var .here))) 4 [1, 2, 3]
  check (.loop (.nat 0) (.nat 5) (.query .mark (.var .here))) 5 []
  check (.loop (.nat 2) (.nat 1)
    (.loop (.nat 2) (.var .here) (.query .mark (.var .here)))) 5 [1, 2, 3, 4]
  check (.call (.ret (.nat 6)) .nil) 6 []

private def failHandler : HeapProgram.HandlerM Cmd (StateM Nat)
  | _, _, .mark, _, _ => do
    modify (· + 1)
    pure ⟨none, 1⟩

#eval show IO Unit from do
  let code : Program CryptoOp Cmd [] .nat :=
    .loop (.nat 5) (.nat 1) (.query .mark (.var .here))
  let actual := ((HeapProgram.compile 4 3 curve curve code).run failHandler [] empty).run 0
  unless actual.1.value.isNone && actual.2 == 1 do
    throw <| IO.userError "failed loop body did not stop before further effects"
  let malformed : HeapProgram.Code Cmd := .loop .nil (.word (natBits 4 0)) (.query .mark (.var []))
  let actual := (malformed.run failHandler [] empty).run 0
  unless actual.1.value.isNone && actual.2 == 0 do
    throw <| IO.userError "non-word loop counter reached its body"

private def H : AddSubgroup curve.Point := ⊥
private instance : Module (ZMod 3) H := EllipticCurveCircuit.subgroupModule curve H (by
  intro P
  have hp : P = 0 := Subtype.ext (by simpa [H] using P.property)
  simp [hp])

#eval show IO Unit from do
  let start := alloc empty (.word [false])
  let step : Address → Store → Id (Run HeapExpression.Result) :=
    fun _ heap => HeapExpression.lift (alloc heap (.word [false]))
  for n in List.range 128 do
    let out := HeapLoop.run step (natBits 7 n) start.value.1 start.value.2
    let some (_, heap) := out.value | throw <| IO.userError "binary controller failed"
    unless heap.count.length == n+1 do
      throw <| IO.userError "binary controller executed wrong number of body calls"
    let nodes := n+1
    let bodyCost := HeapExpression.allocBudget 13 nodes + 1
    unless out.steps ≤ n*(bodyCost+2*7+3)+2*7+2*nodes+3 do
      throw <| IO.userError "binary controller exceeded its pathwise cost bound"

example :
    let args : Args CryptoOp [] [.nat] := .cons (.nat 2) .nil
    (HeapArguments.run (HeapArguments.compile 4 3 curve curve args) [] empty).steps ≤
      5 * HeapArguments.budget 4 5 args := by
  exact (HeapArguments.compile_costed H H (id : BitVec 4 → BitVec 4) (id : BitVec 4 → BitVec 4)
    (r := 3) (Γ := []) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Function.injective_id Function.injective_id PrimitiveCosts.unit (.cons (.nat 2) .nil)
    [] [] () empty empty_represents trivial .nil ⟨by change 2 < 2^4; decide, trivial⟩
    5 _ (by decide) le_rfl).2

end SignaturesTest.HeapProgram

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``HeapArguments.compile_costed, ``HeapArguments.compile_costed_of_budget,
      ``HeapLoop.tick_steps, ``HeapLoop.tick_spec, ``HeapLoop.exponent_natBits,
      ``HeapLoop.run_erase, ``HeapLoop.run_costed, ``HeapLoop.run_refines,
      ``QueryTreeRel.mono, ``QueryTreeRel.symm, ``QueryTreeRel.bind, ``QueryTreeRel.map,
      ``QueryTreeRel.map_eq, ``QueryTreeRel.support_left, ``QueryTreeRel.support_right] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
