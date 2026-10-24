import Proofs.Runtime.CryptoCircuitExecution
import Lean.Util.CollectAxioms

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open Signatures.Runtime CircuitWires WeierstrassCurve

namespace SignaturesTest.CryptoCircuit

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def curve₁ : Affine (ZMod 5) := ⟨0, 0, 0, 1, 1⟩
private def curve₂ : Affine (ZMod 7) := ⟨0, 0, 0, 0, 1⟩
private def P : curve₁.Point := .some 2 1 (by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff, curve₁]
  decide)
private def Q : curve₂.Point := .some 0 1 (by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff, curve₂]
  decide)

private def aig : AIG (Fin 0) := .empty
private def word (n : Nat) : AIG.RefVec aig 6 := blastConst aig (BitVec.ofNat 6 n)
private def bits (n : Nat) : List Bool := List.ofFn (fun i : Fin 6 => (BitVec.ofNat 6 n).getLsbD i)

private def pointRefs {p : Nat} [Fact p.Prime] {W : Affine (ZMod p)} (x : W.Point) :
    Fin 3 → AIG.RefVec aig 6 := fun i => word (EllipticCurveCode.encode x i).val

private def pointBits {p : Nat} [Fact p.Prime] {W : Affine (ZMod p)} (x : W.Point) : List Bool :=
  (List.finRange 3).flatMap (fun i => bits (EllipticCurveCode.encode x i).val)

private def check {a b : Ty CryptoAtom} (name : String) (op : CryptoOp a b)
    (refs : Wires 6 aig a) (expected : List Bool) : IO Unit := do
  let out := CryptoCircuit.execute 3 curve₁ curve₂ aig op refs #v[]
  unless out.value == expected do
    throw <| IO.userError s!"{name}: wrong compiled instruction result"
  let n := aig.decls.size + CryptoCircuit.gates 6 op
  unless out.steps ≤ n*(4*n+10) + CryptoCircuit.outputWidth 6 op*(n+4) + 3 do
    throw <| IO.userError s!"{name}: execution exceeded its cell bound"

-- Every CryptoOp constructor is exercised through the dispatcher and evaluator.
#eval show IO Unit from do
  check "zero" .zero () (bits 0)
  check "one" .one () (bits 1)
  check "add" .add (word 2, word 2) (bits 1)
  check "sub" .sub (word 1, word 2) (bits 2)
  check "mul" .mul (word 2, word 2) (bits 1)
  check "div" .div (word 1, word 2) (bits 2)
  check "division by zero" .div (word 1, word 0) (bits 0)
  check "neg" .neg (word 1) (bits 2)
  check "scalarEq" .scalarEq (word 1, word 2) [false]
  check "keyEq" .keyEq (word 6, word 6) [true]
  check "messageEq" .messageEq (word 6, word 7) [false]
  check "natAdd" .natAdd (word 10, word 20) (bits 30)
  check "natSub" .natSub (word 2, word 5) (bits 0)
  check "natEq" .natEq (word 8, word 8) [true]
  check "natLt" .natLt (word 8, word 9) [true]
  check "finVal" (.finVal 15) (word 15) (bits 15)
  check "finZero" (.finZero 15) () (bits 0)
  check "finOfNat" (.finOfNat 5) (word 17) (bits 5)
  check "full-width Fin" (.finOfNat 63) (word 63) (bits 63)
  check "larger Fin modulus" (.finOfNat 1000) (word 63) (bits 63)
  check "singleton Fin" (.finOfNat 0) (word 63) (bits 0)

#eval show IO Unit from do
  check "zero1" .zero₁ () (pointBits (0 : curve₁.Point))
  check "add1" .add₁ (pointRefs P, pointRefs P) (pointBits (P + P))
  check "sub1" .sub₁ (pointRefs P, pointRefs (-P)) (pointBits (P - -P))
  check "point1Eq" .point₁Eq (pointRefs P, pointRefs (-P)) [false]
  check "zero2" .zero₂ () (pointBits (0 : curve₂.Point))
  check "add2" .add₂ (pointRefs Q, pointRefs Q) (pointBits (Q + Q))
  check "sub2" .sub₂ (pointRefs Q, pointRefs (-Q)) (pointBits (Q - -Q))
  check "point2Eq" .point₂Eq (pointRefs Q, pointRefs Q) [true]

#eval check "scale1" .scale₁ (word 2, pointRefs P) (pointBits ((2 : Nat) • P))
#eval check "scale2" .scale₂ (word 2, pointRefs Q) (pointBits ((2 : Nat) • Q))

-- Nonconstant input ports are read from the supplied bit vector, not evaluated at compile time.
#eval show IO Unit from do
  let x := AIG.mkAtom (AIG.empty : AIG (Fin 1)) 0
  let z := AIG.mkConstCached x.aig false
  let lhs := (AIG.RefVec.empty.push x.ref).push z |>.push z |>.push z |>.push z |>.push z
  let rhs := blastConst x.aig (BitVec.ofNat 6 2)
  for b in [false, true] do
    let out := CryptoCircuit.execute 3 curve₁ curve₂ x.aig .add (lhs, rhs) (Vector.replicate 1 b)
    unless out.value == bits (if b then 0 else 2) do
      throw <| IO.userError "nonconstant scalar addition mismatch"

-- Representation alone does not authorize truncating an overflowing sum.
example : ¬ CryptoCircuit.Safe (r := 3) (w := 6) (K := Unit) (M := Unit)
    (⊥ : AddSubgroup curve₁.Point) (⊥ : AddSubgroup curve₂.Point) .natAdd (63, 1) := by
  change ¬(63 + 1 < 2^6)
  decide
example : CryptoCircuit.Safe (r := 3) (w := 6) (K := Unit) (M := Unit)
    (⊥ : AddSubgroup curve₁.Point) (⊥ : AddSubgroup curve₂.Point) (.finOfNat 1000) 63 := by trivial

end SignaturesTest.CryptoCircuit

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``CryptoCircuit.compile_size, ``CryptoCircuit.compile_correct, ``CryptoCircuit.safe_of_expr_budget,
      ``CryptoCircuit.represents_preserved, ``CryptoCircuit.represented_outputs,
      ``CryptoCircuit.execute_correct, ``CryptoCircuit.execute_steps] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
