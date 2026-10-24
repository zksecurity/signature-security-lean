import Proofs.Runtime.Caliper.RowFoldSource

/-! The joint-state fold is exactly the usual stateful source fold. This
connects the executable traversal to the source evaluator's effect monad. -/
namespace Signatures.Runtime.CaliperBackend.RowFold
open Caliper BoundedSource OracleComp OracleSpec
variable {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {G F I : Type}
    [DecidableEq (key.Value base)] {spec : OracleSpec I}
    (combine : F × (val.Value base × val.Value base) → val.Value base)

theorem sourceStep_fold (sample : OracleComp spec (val.Value base))
    (rows : List ((key.Value base × G) × F)) (accumulator : val.Value base)
    (cache : List (key.Value base × val.Value base)) :
    rows.foldlM (sourceStep (combine := combine) sample) (accumulator, cache) =
      (rows.foldlM (fun (accumulator : val.Value base) (row : (key.Value base × G) × F) => do
        let answer ← QueryImpl.ListCache.handler (fun _ => sample) row.1.1
        pure (combine (row.2, answer, accumulator))) accumulator).run cache := by
  induction rows generalizing accumulator cache with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.foldlM_cons, sourceStep, bind_map_left, StateT.run_bind, bind_assoc, pure_bind]
    congr 1
    funext answer
    exact ih (combine (row.2, answer.1, accumulator)) answer.2

end Signatures.Runtime.CaliperBackend.RowFold
