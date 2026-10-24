import Proofs.Runtime.SchnorrTagged
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.Schnorr

namespace SignaturesTest.SchnorrTagged

private abbrev F := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def primitives := arithmetic F F F Unit Unit PrimitiveCosts.unit

-- A programmed zero answers an ordinary hash without generating a fork point.
example : (taggedHash.denote primitives taggedSemantics (((), (1 : F)), ())).run
    (((1 : F), (2 : F)), [(((), (1 : F)), (0 : F))], []) =
      pure ((0 : F), (((1 : F), (2 : F)), [(((), (1 : F)), (0 : F))], [])) := by
  unfold primitives
  rw [taggedHash_denote]
  simp [cacheMap]

-- Final verification queries the live oracle even when the managed cache was programmed.
example : (taggedFinalHash.denote primitives taggedSemantics (((), (1 : F)), ())).run
    (((1 : F), (2 : F)), [(((), (1 : F)), (0 : F))], []) =
      (fun c : F => (c, (((1 : F), (2 : F)), [(((), (1 : F)), (0 : F))],
        [(((), (1 : F)), c)]))) <$>
          (liftM ((replaySpec F).query (.inr ())) : OracleComp (replaySpec F) F) := by
  unfold primitives
  rw [taggedFinalHash_denote]
  simp [cacheMap, Functor.map_map]

-- A final-query live hit wins over a different managed-cache answer at the same point.
example : (taggedFinalHash.denote primitives taggedSemantics (((), (1 : F)), ())).run
    (((1 : F), (2 : F)), [(((), (1 : F)), (0 : F))], [(((), (1 : F)), (3 : F))]) =
      pure ((3 : F), (((1 : F), (2 : F)), [(((), (1 : F)), (0 : F))],
        [(((), (1 : F)), (3 : F))])) := by
  unfold primitives
  rw [taggedFinalHash_denote]
  simp [cacheMap]

-- Every reply path through a simulated signature has two private draws and no live draw.
example : IsQueryBoundP ((taggedSign.denote primitives taggedSemantics ((), ())).run
    (((1 : F), (2 : F)), [], [])) (fun i => i = Sum.inl (Sum.inr ())) 2 :=
  taggedSign_privateBound PrimitiveCosts.unit () 1 2 [] []

example : IsQueryBoundP ((taggedSign.denote primitives taggedSemantics ((), ())).run
    (((1 : F), (2 : F)), [], [])) (fun i => i = Sum.inr ()) 0 :=
  taggedSign_noChallenge PrimitiveCosts.unit () 1 2 [] []

end SignaturesTest.SchnorrTagged

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``hashProgram_denote, ``finalHashProgram_denote, ``signProgram_denote,
      ``taggedHash_denote, ``taggedFinalHash_denote, ``taggedSign_denote,
      ``taggedSign_noChallenge, ``taggedSign_privateBound, ``taggedHash_liveBound,
      ``taggedFinalHash_liveBound] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
