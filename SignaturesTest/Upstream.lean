import Signatures
import Proofs
import Lean.Util.CollectAxioms

/-! Every theorem in a `Signatures/` statement module (`Statement.lean`, `*Statement.lean`)
depends on exactly `propext`, `Classical.choice` and `Quot.sound`. The list is read from the
environment, so a new public statement is covered without editing this file. -/

open Lean Meta in
run_meta do
  let env ← getEnv
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  let isStatementModule (m : Name) : Bool :=
    m.getRoot == `Signatures && m.getString!.endsWith "Statement"
  let mut checked : Nat := 0
  for (name, info) in env.constants.map₁.toList do
    if name.isInternal then continue
    let some idx := env.getModuleIdxFor? name | continue
    unless isStatementModule env.header.moduleNames[idx.toNat]! do continue
    let .thmInfo _ := info | continue
    let axioms ← collectAxioms name
    unless axioms.size == expected.size && axioms.all expected.contains do
      throwError "{name}: unexpected public theorem axiom footprint {axioms}"
    checked := checked + 1
  unless 40 ≤ checked do
    throwError "expected the public statements, found {checked}"
  logInfo m!"axiom footprint: {checked} public statements use only the three standard axioms"
