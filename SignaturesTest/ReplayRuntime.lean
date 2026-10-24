import Proofs.Runtime.ReplayFork
import Lean.Util.CollectAxioms

/-! Recorded-prefix replay. Compiled tape-cost regressions live in MixedReplay. -/

open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.Replay

namespace SignaturesTest.ReplayRuntime

private def threeQueries : OracleComp (Unit →ₒ Bool) (Bool × Bool × Bool) :=
  OracleComp.queryBind () fun a =>
    OracleComp.queryBind () fun b =>
      OracleComp.queryBind () fun c => pure (a, b, c)

-- Re-execution forces only the recorded prefix. It neither reruns that random draw nor
-- accidentally fixes the challenge or the later random choices.
example (a : Bool) : rerun threeQueries [⟨(), a⟩] =
    OracleComp.queryBind () (fun b => OracleComp.queryBind () (fun c => pure (a, b, c))) := by
  let spine : PFunctor.FreeM.Cursor.Spine threeQueries
      (OracleComp.queryBind () (fun b => OracleComp.queryBind () (fun c => pure (a, b, c)))) :=
    .down a (.root _)
  exact rerun_spine spine

example (a b c : Bool) : splitBefore (spec := Unit →ₒ Bool) () 1
    [⟨(), a⟩, ⟨(), b⟩, ⟨(), c⟩] = some ([⟨(), a⟩], b) := by
  simp [splitBefore]

example (a : Bool) : splitBefore (spec := Unit →ₒ Bool) () 1 [⟨(), a⟩] = none := by
  simp [splitBefore]

-- The implementation that actually reruns from the root has exactly the same joint
-- output distribution as the typed-context fork, including both rejection guards.
example : loggedFork threeQueries (fun _ => 1) () (fun _ => some 1) =
    contextFork threeQueries (fun _ => 1) () (fun _ => some 1) :=
  loggedFork_eq_contextFork _ _ _ _

end SignaturesTest.ReplayRuntime

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``rerun_before, ``rerun_log_before, ``splitBefore_trace, ``splitBefore_before,
      ``rerun_log_completion, ``loggedFork_eq_contextFork] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
