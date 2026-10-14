import Signatures.Runtime.PrimeFieldOps
import Signatures.Runtime.WordCircuit
import Lean.Util.CollectAxioms

open Std.Sat Std.Tactic.BVDecide BVExpr.bitblast
open Signatures.Runtime

namespace SignaturesTest.PrimitiveBits

private def checkWord {A : Type} [Hashable A] [DecidableEq A] {w : Nat}
    (result : AIG.RefVecEntry A w) (assign : A → Bool) (expected : Nat) : IO Unit := do
  for i in List.finRange w do
    unless AIG.denote assign ⟨result.aig, result.vec.get i i.isLt⟩ ==
        (BitVec.ofNat w expected).getLsbD i do
      throw <| IO.userError s!"wrong bit {i.val} of expected word {expected}"

-- Exhaustive small-word tests run one symbolic circuit on every input assignment.
#eval show IO Unit from do
  let a := blastVar (AIG.empty : AIG BVBit) (w := 4) ⟨0⟩
  let b := blastVar a.aig (w := 4) ⟨1⟩
  have hb := AIG.LawfulVecOperator.le_size (f := blastVar) a.aig (len := 4) ⟨1⟩
  let input := AIG.BinaryRefVec.mk (a.vec.cast hb) b.vec
  let sub := WordCircuit.subtract b.aig input
  let add := blastAdd b.aig input
  let eq := BVPred.mkEq b.aig input
  let lt := BVPred.mkUlt b.aig input
  for x in List.range 16 do
    for y in List.range 16 do
      let assign := fun v : BVBit =>
        (BitVec.ofNat 4 (if v.var == 0 then x else y)).getLsbD v.idx.val
      checkWord sub assign (x - y)
      if x + y < 16 then checkWord add assign (x + y)
      unless AIG.denote assign eq == (x == y) && AIG.denote assign lt == (x < y) do
        throw <| IO.userError "word comparison mismatch"
  unless sub.aig.decls.size ≤ b.aig.decls.size + 33 * 4 do
    throw <| IO.userError "word subtraction size mismatch"

#eval show IO Unit from do
  let aig : AIG Unit := .empty
  for x in List.range 5 do
    let xr := blastConst aig (BitVec.ofNat 6 x)
    checkWord (PrimeFieldCircuit.negate aig xr 5).result (fun _ => false) ((5 - x) % 5)
    for y in List.range 5 do
      let input := AIG.BinaryRefVec.mk xr (blastConst aig (BitVec.ofNat 6 y))
      checkWord (PrimeFieldCircuit.add aig input 5).result (fun _ => false) ((x + y) % 5)
  checkWord (PrimeFieldCircuit.zero aig (w := 6)).result (fun _ => false) 0
  checkWord (PrimeFieldCircuit.one aig (w := 6)).result (fun _ => false) 1
  for x in List.range 16 do
    let xr := blastConst aig (BitVec.ofNat 4 x)
    checkWord (WordCircuit.finOfNat aig xr 0) (fun _ => false) 0
    checkWord (WordCircuit.finOfNat aig xr 4) (fun _ => false) (x % 5)
    checkWord (WordCircuit.finOfNat aig xr 7) (fun _ => false) (x % 8)
    checkWord (WordCircuit.finOfNat aig xr 15) (fun _ => false) x
  checkWord (WordCircuit.finOfNat aig (blastConst aig (0#0)) 0) (fun _ => false) 0

end SignaturesTest.PrimitiveBits

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``PrimeFieldCircuit.add_correct, ``PrimeFieldCircuit.add_size,
      ``PrimeFieldCircuit.negate_correct, ``PrimeFieldCircuit.eq_correct,
      ``WordCircuit.add_correct, ``WordCircuit.subtract_correct, ``WordCircuit.subtract_size,
      ``WordCircuit.eq_correct, ``WordCircuit.eq_encoded_correct,
      ``WordCircuit.lt_correct, ``WordCircuit.finOfNat_correct,
      ``WordCircuit.finVal_correct, ``WordCircuit.finZero_correct] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
