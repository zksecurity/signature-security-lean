import Signatures.Runtime.SchnorrSelection
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrSelection

private abbrev F := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def primitives := arithmetic F F F Unit Nat PrimitiveCosts.unit
private def entries : List ((Nat × F) × F) := [((3, 1), 2), ((2, 0), 4), ((1, 2), 3)]

-- Newest-first storage is converted to the chronological live-query ordinal.
example : (liveIndex.run primitives ((3, 1), entries, ())).value = (true, 2) := by
  rw [Expr.run_value]
  unfold primitives
  rw [liveIndex_denote]
  decide

example : (liveIndex.run primitives ((1, 2), entries, ())).value = (true, 0) := by
  rw [Expr.run_value]
  unfold primitives
  rw [liveIndex_denote]
  decide

-- A missing target is distinguished from ordinal zero.
example : (liveIndex.run primitives ((4, 1), entries, ())).value = (false, 3) := by
  rw [Expr.run_value]
  unfold primitives
  rw [liveIndex_denote]
  decide

example : (verifyObserved.run primitives (((1 : Nat), (2 : F), (3 : F)), 1, 1, 1, ())).value = true := by
  unfold primitives
  rw [verifyObserved_run]
  decide

example : (verifyObserved.run primitives (((1 : Nat), (2 : F), (4 : F)), 1, 1, 1, ())).value = false := by
  unfold primitives
  rw [verifyObserved_run]
  decide

-- The final verification query is the extra allowed slot; the next ordinal is rejected.
example : (guardIndex.run primitives ((true, 2), 2, ())).value = (true, 2) := by
  unfold primitives
  rw [guardIndex_run]
  rfl

example : (guardIndex.run primitives ((true, 2), 1, ())).value = (false, 0) := by
  unfold primitives
  rw [guardIndex_run]
  rfl

example : (guardIndex.run primitives ((false, 0), 2, ())).value = (false, 0) := by
  unfold primitives
  rw [guardIndex_run]
  rfl

end SignaturesTest.SchnorrSelection

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``findStep_fold, ``liveIndexBody_denote, ``liveIndex_denote,
      ``liveIndexBody_steps, ``liveIndexFold_steps, ``liveIndex_steps, ``verifyObserved_run,
      ``guardIndex_run, ``selectCode_run, ``selectCode_bound, ``selectCode_erase,
      ``selectValue_forkPoint] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
