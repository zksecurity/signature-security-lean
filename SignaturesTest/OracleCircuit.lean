import Proofs.Runtime.OracleCircuit
import Lean.Util.CollectAxioms

open OracleComp Signatures.Runtime Signatures.Runtime.OracleCircuit

namespace SignaturesTest.OracleCircuit

private def invertFirstBit : CircuitExecution.Code :=
  ⟨[.input []], [([], true)]⟩

private def inspectKey : Adversary :=
  .ret (.op (.circuit invertFirstBit) (.var .here))

/-- A raw representation bit, rather than only group arithmetic, controls this result. -/
example : inspectKey.main [true] = pure [false] := rfl
example : inspectKey.main [false] = pure [true] := rfl

private def inspectHash : Adversary :=
  .bind (.query .hash (.var .here))
    (.ret (.op (.circuit invertFirstBit) (.var .here)))

/-- Replies remain inspectable bit strings, including on adaptive query paths. -/
example (input : List Bool) : inspectHash.main input =
    OracleComp.queryBind (spec := spec) (.hash input)
      (fun answer => pure (invertFirstBit.run answer).value) := rfl

end SignaturesTest.OracleCircuit

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``ofCircuit_correct, ``ofCircuit_cost, ``ofCircuit_steps] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
