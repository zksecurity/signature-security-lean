import Proofs.Runtime.PrimeFieldCircuit
import Proofs.Runtime.BitSampling
import Proofs.Runtime.Schnorr
import Lean.Util.CollectAxioms

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open Signatures.Runtime

namespace SignaturesTest.BitComplexity

private def checkExtraction (p w z z' c c' expected : Nat) : IO Unit := do
  let aig : AIG Unit := .empty
  let result := PrimeFieldCircuit.extract aig
    (blastConst aig (BitVec.ofNat w z)) (blastConst aig (BitVec.ofNat w z'))
    (blastConst aig (BitVec.ofNat w c)) (blastConst aig (BitVec.ofNat w c')) p
  let actual := List.ofFn fun i : Fin w =>
    AIG.denote (fun _ => false) ⟨result.aig, result.vec.get i i.isLt⟩
  let want := List.ofFn fun i : Fin w => (BitVec.ofNat w expected).getLsbD i
  unless actual == want do
    throw <| IO.userError s!"wrong extraction modulo {p}: {actual} != {want}"

-- These execute the generated circuits, including total division at zero.
#eval checkExtraction 5 6 3 1 2 1 2
#eval checkExtraction 5 6 1 3 1 2 2
#eval checkExtraction 5 6 2 2 1 3 0
#eval checkExtraction 5 6 2 1 1 1 0
#eval checkExtraction 17 10 16 1 3 1 16

-- Variable inputs prevent the optimizer from replacing the entire circuit with constants.
#eval show IO Unit from do
  let a := blastVar (AIG.empty : AIG BVBit) (w := 6) ⟨0⟩
  let b := blastVar a.aig (w := 6) ⟨1⟩
  have hb := AIG.LawfulVecOperator.le_size (f := blastVar) a.aig (len := 6) ⟨1⟩
  let c := blastVar b.aig (w := 6) ⟨2⟩
  have hc := AIG.LawfulVecOperator.le_size (f := blastVar) b.aig (len := 6) ⟨2⟩
  let d := blastVar c.aig (w := 6) ⟨3⟩
  have hd := AIG.LawfulVecOperator.le_size (f := blastVar) c.aig (len := 6) ⟨3⟩
  let result := PrimeFieldCircuit.extract d.aig (a.vec.cast (hb.trans (hc.trans hd)))
    (b.vec.cast (hc.trans hd)) (c.vec.cast hd) d.vec 5
  unless d.aig.decls.size < result.aig.decls.size &&
      result.aig.decls.size ≤ d.aig.decls.size + 102 * 6^3 + 137 * 6^2 + 93 * 6 do
    throw <| IO.userError "unexpected nonconstant extraction circuit size"

-- The Boolean circuit implements exactly the already-costed arithmetic extractor.
example {p w : Nat} [Fact p.Prime] (hfit : p * p ≤ 2 ^ w) (hp : 2 < p)
    (aig : AIG Unit) (zr zr' cr cr' : AIG.RefVec aig w) (assign : Unit → Bool)
    (z z' c c' : ZMod p) (cost : PrimitiveCosts)
    (hz : PrimeFieldCircuit.Represents assign aig zr (BitVec.ofNat w z.val))
    (hz' : PrimeFieldCircuit.Represents assign aig zr' (BitVec.ofNat w z'.val))
    (hc : PrimeFieldCircuit.Represents assign aig cr (BitVec.ofNat w c.val))
    (hc' : PrimeFieldCircuit.Represents assign aig cr' (BitVec.ofNat w c'.val)) :
    PrimeFieldCircuit.Represents assign
      (PrimeFieldCircuit.extract aig zr zr' cr cr' p).aig
      (PrimeFieldCircuit.extract aig zr zr' cr cr' p).vec
      (BitVec.ofNat w (Schnorr.extract.run
        (arithmetic (ZMod p) (ZMod p) (ZMod p) Unit Unit cost) (z, z', c, c', ())).value.val) := by
  rw [Schnorr.extract_run]
  exact PrimeFieldCircuit.extract_correct hfit hp aig zr zr' cr cr' assign z z' c c' hz hz' hc hc'

example (bits : Nat) (f : (Fin bits → Bool) → Fin 3) : ¬ BitSampling.Balanced f :=
  BitSampling.not_balanced_prime 3 bits (by decide) (by decide) f

end SignaturesTest.BitComplexity

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``BitCircuit.add_size, ``BitCircuit.mul_size, ``BitCircuit.mod_size,
      ``PrimeFieldCircuit.mulMod_correct, ``PrimeFieldCircuit.inverse_correct,
      ``PrimeFieldCircuit.extract_correct, ``PrimeFieldCircuit.extract_size,
      ``PrimeFieldCircuit.standard_width, ``BitSampling.not_balanced_prime] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
