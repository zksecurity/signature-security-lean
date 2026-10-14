import Signatures.Runtime.SchnorrCacheRefinement
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

/-! Cache collision preservation and message/commitment key regressions.
Tagged and compiled replay-handler regressions are in SchnorrTagged and SchnorrReplayMachine. -/

open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrCache

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private def primitives := arithmetic F F F Unit Unit PrimitiveCosts.unit

private theorem keyEq (x y : Unit × F) :
    hashEq.denote primitives (x, y, ()) = decide (x = y) := hashEq_value _ x y

-- Programming a collision does not overwrite even a zero-valued cached challenge.
example : ((cacheProgram (val := scalar) hashEq).run primitives
    (((), (1 : F)), (4 : F), [(((), (1 : F)), (0 : F))], ())).value =
      [(((), (1 : F)), (0 : F))] := by
  rw [cacheProgram_value primitives hashEq keyEq]
  simp [lookupValue]

-- Identical messages with different commitments are different hash inputs.
example : hashEq.denote primitives (((), (1 : F)), ((), (2 : F)), ()) = false := by
  rw [keyEq]
  decide

end SignaturesTest.SchnorrCache

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``cacheGetExpr_run, ``cacheGetExpr_denote, ``cacheGetExpr_bound,
      ``cacheProgram_value, ``cacheProgram_steps_le, ``managedGet_run, ``managedGet_bound,
      ``signCached_run, ``signCached_denote, ``signCached_bound, ``liveGet_refines,
      ``managedGet_refines, ``signCached_refines, ``cacheProgram_managedState] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
