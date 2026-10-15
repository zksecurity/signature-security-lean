import Signatures.Runtime.BackendSchnorrAGMFlattenBudget
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open PFunctor Schnorr.AGM
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.SchnorrAGM.Native

namespace SignaturesTest.BackendSchnorrAGMFlatten

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7

-- Generator, public key, then a signing reply with challenge two and response
-- five. Chronological coefficients (3,4,2) flatten to (6,0) in ZMod 7.
example (cost : PrimitiveCosts) :
    (Flatten.expression (Γ := [message])).denote (arithmetic F F F Nat Nat cost)
      ([(1, 0), (0, 1), (5, 5)], [3, 4, 2], 123, ()) = (6, 0) := by
  rw [Flatten.expression_denote]
  decide

-- Missing coefficients are zero even on malformed input; the original source
-- convention has no length-equality precondition.
example (cost : PrimitiveCosts) :
    (Flatten.expression (Γ := [])).denote (arithmetic F F F Nat Nat cost)
      ([(1, 0), (0, 1), (5, 5)], [3], ()) = (3, 0) := by
  rw [Flatten.expression_denote]
  decide

-- Surplus coefficients cannot introduce another received group element.
example (cost : PrimitiveCosts) :
    (Flatten.expression (Γ := [])).denote (arithmetic F F F Nat Nat cost)
      ([(1, 0), (0, 1), (5, 5)], [3, 4, 2, 6], ()) = (6, 0) := by
  rw [Flatten.expression_denote]
  decide

-- Equal affine representations still have separate positional coefficients.
example (cost : PrimitiveCosts) :
    (Flatten.expression (Γ := [])).denote (arithmetic F F F Nat Nat cost)
      ([(1, 2), (1, 2)], [3, 5], ()) = (1, 2) := by
  rw [Flatten.expression_denote]
  decide

example (cost : PrimitiveCosts) :
    (Flatten.expression (Γ := [])).denote (arithmetic F F F Nat Nat cost)
      ([], [3, 4, 2], ()) = (0, 0) := by
  rw [Flatten.expression_denote]
  decide

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Flatten.body_denote, ``Flatten.sumRows_denote, ``Flatten.expression_denote,
      ``Flatten.value_source, ``Flatten.source, ``Flatten.body_time, ``Flatten.sumRows_time,
      ``Flatten.expression_time, ``Flatten.code_cost, ``Flatten.output_size, ``Flatten.description] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  for name in #[``Flatten.code, ``Flatten.source, ``Flatten.code_cost] do
    forallTelescope (← getConstInfo name).type fun params _ => do
      for param in params do
        let type ← inferType param
        if type.isAppOf ``Finite || type.isAppOf ``Fintype then
          throwError "{name}: unexpected finite-domain premise"
        for forbidden in #[``Flatten.code, ``Flatten.expression, ``Flatten.flattenTime,
            ``Flatten.sumTime, ``Flatten.sumRows, ``AGM.attachTable, ``AttachCompiler.tableTime] do
          if (type.find? (fun e => e.isConstOf forbidden)).isSome then
            throwError "{name}: assumes completed flattening or coefficient-matching efficiency"

end SignaturesTest.BackendSchnorrAGMFlatten
