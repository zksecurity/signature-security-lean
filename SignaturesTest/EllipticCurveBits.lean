import Proofs.Runtime.EllipticCurveCircuit
import Lean.Util.CollectAxioms

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open Signatures.Runtime FieldProgram EllipticCurveCode WeierstrassCurve

namespace SignaturesTest.EllipticCurveBits

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def curve : Affine (ZMod 5) := ⟨0, 0, 0, 1, 1⟩

private def P : curve.Point := .some 0 1 (by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff, curve])

private def Q : curve.Point := .some 2 1 (by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff, curve]
  decide)

private def pointRefs {W : Affine (ZMod 5)} (aig : AIG Unit) (P : W.Point) : Fin 3 → AIG.RefVec aig 6 :=
  fun i => blastConst aig (BitVec.ofNat 6 (encode P i).val)

private def checkOutput {k : Nat} {aig : AIG Unit} (out : Bundle aig 6 k)
    (expected : Fin k → ZMod 5) : IO Unit := do
  for i in List.finRange k do
    for j in List.finRange 6 do
      unless AIG.denote (fun _ => false) ⟨out.graph, (out.refs i).get j j.isLt⟩ ==
          (BitVec.ofNat 6 (expected i).val).getLsbD j do
        throw <| IO.userError s!"wrong curve output {i.val}, bit {j.val}"

private def checkPair (x y : curve.Point) : IO Unit := do
  let aig : AIG Unit := .empty
  let xr := pointRefs aig x
  let yr := pointRefs aig y
  checkOutput (EllipticCurveCircuit.neg curve aig xr) (encode (Affine.Point.neg x))
  checkOutput (EllipticCurveCircuit.add curve aig xr yr) (encode (Affine.Point.add x y))
  checkOutput (EllipticCurveCircuit.sub curve aig xr yr)
    (encode (Affine.Point.add x (Affine.Point.neg y)))
  unless AIG.denote (fun _ => false) (EllipticCurveCircuit.equal 5 aig xr yr) == (x == y) do
    throw <| IO.userError "curve equality mismatch"
  checkOutput (EllipticCurveCircuit.zero aig) (encode (Affine.Point.zero : curve.Point))

#eval checkPair .zero P
#eval checkPair P .zero
#eval checkPair P P
#eval checkPair P Q
#eval checkPair P (Affine.Point.neg P)
#eval checkPair (Affine.Point.neg P) Q

private def torsionCurve : Affine (ZMod 5) := ⟨0, 0, 0, 1, 0⟩
private def torsionPoint : torsionCurve.Point := .some 0 0 (by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff, torsionCurve])
private def generalCurve : Affine (ZMod 5) := ⟨1, 2, 1, 3, 0⟩
private def generalPoint : generalCurve.Point := .some 0 0 (by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff, generalCurve])

#eval show IO Unit from do
  let aig : AIG Unit := .empty
  let t := pointRefs aig torsionPoint
  checkOutput (EllipticCurveCircuit.add torsionCurve aig t t) (fun _ => 0)
  let g := pointRefs aig generalPoint
  checkOutput (EllipticCurveCircuit.neg generalCurve aig g) ![1, 0, 4]
  checkOutput (EllipticCurveCircuit.add generalCurve aig g g)
    (encode (Affine.Point.add generalPoint generalPoint))

-- This input is not constant-foldable; verify actual gate allocation and its cap.
#eval show IO Unit from do
  let input := blastVar (AIG.empty : AIG BVBit) (w := 6) ⟨0⟩
  let refs := ![blastConst input.aig (1#6), blastConst input.aig (0#6), input.vec]
  let out := EllipticCurveCircuit.add curve input.aig refs refs
  unless input.aig.decls.size < out.graph.decls.size &&
      out.graph.decls.size ≤ input.aig.decls.size + 4080 * 6^3 + 20897 * 6^2 + 12774 * 6 do
    throw <| IO.userError "curve addition gate count mismatch"

-- Binding shares the computed intermediate, and selections exercise both branches.
#eval show IO Unit from do
  let aig : AIG Unit := .empty
  let code : Code 2 := .bind (.var 0 + .var 1)
    (Code.ifEq (.var 0) 0 7 ((.var 0 * .var 0) / .var 1))
  for x in List.range 5 do
    for y in List.range 5 do
      let env : Fin 2 → ZMod 5 := ![x, y]
      let refs := fun i => blastConst aig (BitVec.ofNat 6 (env i).val)
      let out := compileMany 5 (fun _ : Fin 1 => code) aig refs
      checkOutput out (fun _ => code.eval env)

end SignaturesTest.EllipticCurveBits

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``Code.compile_correct, ``Code.compile_size,
      ``compileMany_correct, ``compileMany_size, ``encode_injective,
      ``negCode_correct, ``addCode_correct, ``addCode_gates,
      ``EllipticCurveCircuit.zero_correct, ``EllipticCurveCircuit.neg_correct,
      ``EllipticCurveCircuit.add_correct, ``EllipticCurveCircuit.add_size,
      ``EllipticCurveCircuit.sub_correct, ``EllipticCurveCircuit.sub_size,
      ``EllipticCurveCircuit.equal_correct, ``EllipticCurveCircuit.equal_size] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
