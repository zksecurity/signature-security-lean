import Signatures.Runtime.PrimitiveCode
import Lean.Util.CollectAxioms

open Std.Sat Signatures.Runtime CircuitWires FixedPorts WeierstrassCurve

namespace SignaturesTest.PrimitiveCode

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def curve : Affine (ZMod 3) := ⟨0, 0, 0, 1, 1⟩
private def P : curve.Point := .some 0 1 (by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff, curve])
private def H : AddSubgroup curve.Point := ⊤
private def point : H := ⟨P, by trivial⟩
private abbrev Base := cryptoBase (ZMod 3) H H (BitVec 4) (BitVec 4)
private def bits (n : Nat) : List Bool := List.ofFn (fun i : Fin 4 => (BitVec.ofNat 4 n).getLsbD i)

-- All operand shapes, including the two distinct group tags, use fresh bits.
private def checkPorts {a b : Ty CryptoAtom} (op : CryptoOp a b) (x : a.Value Base) : IO Unit := do
  let layout := inputLayout op
  let input := Vector.ofFn (layout.encode H H id id x)
  let ports := layout.ports 4
  unless ports.graph.decls.size == 1 + input.size do
    throw <| IO.userError "incorrect fresh input-node count"
  unless layout.width 4 ≤ 24 do
    throw <| IO.userError "operand ports exceed six words"
  let actual := CircuitExecution.evaluate ports.graph (outputs ports.refs) input
  unless actual.value == CryptoCircuit.portBits H H id id x do
    throw <| IO.userError "typed operand wiring changes the bit order"

#eval show IO Unit from do
  checkPorts .zero ()
  checkPorts .one ()
  checkPorts .add (1, 2)
  checkPorts .sub (1, 2)
  checkPorts .mul (1, 2)
  checkPorts .div (1, 2)
  checkPorts .neg 2
  checkPorts .zero₁ ()
  checkPorts .zero₂ ()
  checkPorts .add₁ (point, -point)
  checkPorts .add₂ (-point, point)
  checkPorts .sub₁ (0, point)
  checkPorts .sub₂ (point, 0)
  checkPorts .scale₁ (2, point)
  checkPorts .scale₂ (1, -point)
  checkPorts .scalarEq (2, 1)
  checkPorts .point₁Eq (point, 0)
  checkPorts .point₂Eq (0, point)
  checkPorts .keyEq (3, 7)
  checkPorts .messageEq (8, 15)
  checkPorts .natAdd (3, 7)
  checkPorts .natSub (3, 7)
  checkPorts .natEq (9, 9)
  checkPorts .natLt (10, 9)
  checkPorts (.finVal 1000) ⟨15, by decide⟩
  checkPorts (.finZero 1000) ()
  checkPorts (.finOfNat 1000) 15

-- Compile once; reuse the exact same code for different online operands.
#eval show IO Unit from do
  let code := CryptoCircuit.precompile 4 3 curve curve .add
  let m := (inputLayout .add).width 4
  let n := 1 + m + CryptoCircuit.gates 4 .add
  unless code.cells ≤ n*(2*n+m+4) + 4*(n+2) + 2 do
    throw <| IO.userError "precompiled code exceeds its cell-size bound"
  for x in [0, 1, 2] do
    for y in [0, 1, 2] do
      let out := code.run (bits x ++ bits y)
      unless out.value == bits ((x+y)%3) do
        throw <| IO.userError "precompiled scalar addition mismatch"
      unless out.steps ≤ n*(4*n+m+10)+4*(n+4)+3 do
        throw <| IO.userError "precompiled execution exceeds its bound"

#eval show IO Unit from do
  let sub := CryptoCircuit.precompile 4 3 curve curve .natSub
  let fin := CryptoCircuit.precompile 4 3 curve curve (.finOfNat 1000)
  let eq := CryptoCircuit.precompile 4 3 curve curve .point₁Eq
  let zero := CryptoCircuit.precompile 4 3 curve curve .zero
  unless (sub.run (bits 2 ++ bits 5)).value == bits 0 do
    throw <| IO.userError "natural subtraction did not saturate"
  unless (fin.run (bits 15)).value == bits 15 do
    throw <| IO.userError "wide Fin modulus did not preserve its operand"
  for q in [point, -point, 0] do
    let input := Vector.ofFn ((inputLayout .point₁Eq).encode (r := 3) (w := 4) H H id id (point, q))
    unless (eq.run input.toList).value == [decide (point = q)] do
      throw <| IO.userError "precompiled group equality mismatch"
  unless (zero.run []).value == bits 0 do
    throw <| IO.userError "zero-input code mismatch"

-- Zero-width port construction itself is valid, independently of the prime
-- hypotheses (which correctly rule out zero-width arithmetic refinements).
example : ((Layout.pair (.atom .point₁) (.atom .point₂)).ports 0).graph.decls.size = 1 := by
  rw [Layout.ports_size]
  rfl

end SignaturesTest.PrimitiveCode

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``InputCircuit.build_size, ``InputCircuit.build_correct,
      ``InputCircuit.wires_get, ``Layout.represents, ``Layout.ports_correct,
      ``Layout.ports_size, ``inputWidth_le, ``CircuitExecution.lower_run,
      ``CircuitExecution.lower_cells, ``CircuitExecution.Code.run_length,
      ``CryptoCircuit.precompile_length, ``CryptoCircuit.precompile_correct,
      ``CryptoCircuit.precompile_steps, ``CryptoCircuit.precompile_cells] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
