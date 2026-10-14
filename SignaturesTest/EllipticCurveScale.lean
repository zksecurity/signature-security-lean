import Signatures.Runtime.EllipticCurveScale
import Lean.Util.CollectAxioms

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open Signatures.Runtime FieldProgram EllipticCurveCode WeierstrassCurve

namespace SignaturesTest.EllipticCurveScale

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def curve : Affine (ZMod 5) := ⟨0, 0, 0, 1, 1⟩
private def Q : curve.Point := .some 2 1 (by
  norm_num [Affine.nonsingular_iff, Affine.equation_iff, curve]
  decide)

private def subgroup : AddSubgroup curve.Point where
  carrier := {P | 3 • P = 0}
  zero_mem' := nsmul_zero 3
  add_mem' := by
    intro a b ha hb
    change 3 • a = 0 at ha
    change 3 • b = 0 at hb
    change 3 • (a + b) = 0
    simp only [nsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    change 3 • a = 0 at ha
    change 3 • (-a) = 0
    exact (neg_nsmul a 3).trans ((congrArg Neg.neg ha).trans neg_zero)

private instance : Module (ZMod 3) subgroup :=
  EllipticCurveCircuit.subgroupModule curve subgroup (fun P => Subtype.ext P.property)

private def base : subgroup := ⟨Q, by change 3 • Q = 0; decide +kernel⟩

-- Scalar and coordinate moduli, and their word widths, are deliberately different.
example {aig : AIG Unit} (scalar : AIG.RefVec aig 2)
    (refs : Fin 3 → AIG.RefVec aig 6) (assign : Unit → Bool) (x : ZMod 3)
    (hx : PrimeFieldCircuit.Represents assign aig scalar (BitVec.ofNat 2 x.val))
    (hQ : EllipticCurveCircuit.RepresentsPoint assign aig refs (base : curve.Point)) :
    EllipticCurveCircuit.RepresentsPoint assign
      (EllipticCurveCircuit.scale curve aig scalar refs).graph
      (EllipticCurveCircuit.scale curve aig scalar refs).refs ((x • base : subgroup) : curve.Point) :=
  EllipticCurveCircuit.scale_correct (by decide) (by decide) (by decide)
    curve subgroup aig scalar refs assign x base hx hQ

private def checkScalar (v n : Nat) : IO Unit := do
  let aig : AIG Unit := .empty
  let scalar := blastConst aig (BitVec.ofNat v n)
  let refs := fun i => blastConst aig (BitVec.ofNat 6 (encode Q i).val)
  let out := EllipticCurveCircuit.scale curve aig scalar refs
  let expected := encode ((BitVec.ofNat v n).toNat • Q)
  for i in List.finRange 3 do
    for j in List.finRange 6 do
      unless AIG.denote (fun _ => false) ⟨out.graph, (out.refs i).get j j.isLt⟩ ==
          (BitVec.ofNat 6 (expected i).val).getLsbD j do
        throw <| IO.userError s!"scalar {n}, width {v}, coordinate {i.val}, bit {j.val}"
  unless out.graph.decls.size ≤ aig.decls.size + v * (8160*6^3 + 41794*6^2 + 25557*6) do
    throw <| IO.userError "scalar multiplication gate count mismatch"

#eval checkScalar 0 0
#eval checkScalar 2 0
#eval checkScalar 2 1
#eval checkScalar 2 2
#eval checkScalar 2 3
#eval checkScalar 3 1

-- A secret scalar input must influence the output; it is not a host-language branch.
#eval show IO Unit from do
  let scalar := blastVar (AIG.empty : AIG BVBit) (w := 1) ⟨0⟩
  let refs := fun i => blastConst scalar.aig (BitVec.ofNat 6 (encode Q i).val)
  let out := EllipticCurveCircuit.scale curve scalar.aig scalar.vec refs
  for b in [false, true] do
    let expected := encode (if b then Q else (0 : curve.Point))
    for i in List.finRange 3 do
      for j in List.finRange 6 do
        unless AIG.denote (fun _ => b) ⟨out.graph, (out.refs i).get j j.isLt⟩ ==
            (BitVec.ofNat 6 (expected i).val).getLsbD j do
          throw <| IO.userError "secret scalar selector mismatch"

end SignaturesTest.EllipticCurveScale

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``WordCircuit.exponent_word,
      ``selectMany_correct, ``selectMany_size,
      ``EllipticCurveCircuit.scaleBits_correct, ``EllipticCurveCircuit.scaleBits_size,
      ``EllipticCurveCircuit.scale_word_correct, ``EllipticCurveCircuit.scale_correct,
      ``EllipticCurveCircuit.scale_size] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
