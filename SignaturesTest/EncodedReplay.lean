import Signatures.Runtime.ReplayScan
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.Schnorr

namespace SignaturesTest.EncodedReplay

attribute [local implicit_reducible] FreeMonoid PFunctor.Idx

private def tape : Replay.Tape (replaySpec Nat) :=
  [⟨.inl (.inr ()), (9 : Nat)⟩, ⟨.inl (.inl 3), (⟨2, by omega⟩ : Fin 4)⟩,
    ⟨.inr (), (7 : Nat)⟩, ⟨.inl (.inr ()), (6 : Nat)⟩, ⟨.inr (), (4 : Nat)⟩]

-- The first live challenge follows two private draws, neither of which is a hash.
example : splitCells 0 (encodeTape tape) = some ([(0, 9, 0), (5, 0, 2)], 7) := rfl

-- A later fork replays prior live answers too, but never the selected live answer.
example : splitCells 1 (encodeTape tape) =
    some ([(0, 9, 0), (5, 0, 2), (1, 7, 0), (0, 6, 0)], 4) := rfl

example : splitCells 2 (encodeTape tape) = none := rfl

example : scanView ((encodeTape tape).foldl scanStep (1, false, 0, 0, [])) =
    some ([(0, 9, 0), (5, 0, 2), (1, 7, 0), (0, 6, 0)], 4) := rfl

example : ((encodeTape tape).foldl scanStep (1, false, 0, 0, [])).2.2.2.1 = 4 := rfl

-- The empty prefix means the first query is fresh, not a zero-filled replay cell.
example (main : OracleComp (replaySpec Nat) Nat) :
    indexedLoggedRun main [] = (fun p => (p.1, encodeTape p.2)) <$> main.withQueryLog :=
  indexedLoggedRun_empty main

end SignaturesTest.EncodedReplay

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``indexedRun_fresh, ``indexedRun_spine, ``indexedRun_log_spine,
      ``splitCells_encode, ``indexedFork_eq_loggedFork, ``expand_indexedFork,
      ``scanBody_denote, ``scanFold_steps, ``scanFold_view, ``scanCode_denote,
      ``scanCode_steps, ``scanStep_size] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
