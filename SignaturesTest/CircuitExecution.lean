import Proofs.Runtime.CircuitExecution
import Proofs.Runtime.PrimeFieldCircuit
import Lean.Util.CollectAxioms

open Std.Sat
open Signatures.Runtime CircuitExecution

namespace SignaturesTest.CircuitExecution

-- Both ordinary and complemented outputs are read; the cached builder folds the self-fan-in gate
-- `⟨xy.ref, xy.ref⟩` back to `xy` (idempotency), so the circuit is one AND gate.
#eval show IO Unit from do
  let x := AIG.mkAtomCached (AIG.empty : AIG (Fin 2)) 0
  let y := AIG.mkAtomCached x.aig 1
  let xy := AIG.mkGateCached y.aig ⟨x.ref.cast (AIG.LawfulOperator.le_size (f := AIG.mkAtomCached) x.aig 1), y.ref⟩
  let shared := AIG.mkGateCached xy.aig ⟨xy.ref, xy.ref⟩
  let refs := [shared.ref, ⟨shared.ref.gate, true, shared.ref.hgate⟩]
  let n := shared.aig.decls.size
  unless ((compile shared.aig).map Instr.cells).sum ≤ n * (2*n + 2 + 3) do
    throw <| IO.userError "compiled unary-address code exceeds its size bound"
  for a in [false, true] do
    for b in [false, true] do
      let input := Vector.ofFn (fun i : Fin 2 => if i.val = 0 then a else b)
      let out := evaluate shared.aig refs input
      unless out.value == [a && b, !(a && b)] do
        throw <| IO.userError "compiled AIG result mismatch"
      unless out.steps ≤ n * (4*n + 2 + 10) + 2*(n+4) + 3 do
        throw <| IO.userError "compiled AIG execution exceeds its cell bound"
      unless (execute shared.aig input).value.length == n do
        throw <| IO.userError "one memory bit must be stored per declaration"

#eval show IO Unit from do
  let aig : AIG (Fin 0) := .empty
  let input : Vector Bool 0 := #v[]
  let out := evaluate aig [AIG.mkConstCached aig false, AIG.mkConstCached aig true] input
  unless out.value == [false, true] do
    throw <| IO.userError "zero-input circuit mismatch"
  unless (evaluate aig [] input).value == [] do
    throw <| IO.userError "zero-output circuit mismatch"
  unless (read [(), (), ()] [true]).value == false do
    throw <| IO.userError "out-of-range memory read mismatch"

-- Existing representation theorems transfer directly to the executable evaluator.
example {m w : Nat} (aig : AIG (Fin m)) (refs : AIG.RefVec aig w)
    (input : Vector Bool m) (value : BitVec w)
    (h : PrimeFieldCircuit.Represents (fun i => input[i]) aig refs value) :
    (evaluate aig (List.ofFn (fun i : Fin w => refs.get i i.isLt)) input).value =
      List.ofFn (fun i : Fin w => value.getLsbD i) := by
  rw [evaluate_correct, List.map_ofFn]
  congr 1
  funext i
  exact h i i.isLt

end SignaturesTest.CircuitExecution

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``compile_cells, ``execute_length, ``execute_steps, ``execute_correct,
      ``evaluate_correct, ``evaluate_steps] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
