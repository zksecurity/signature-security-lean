import Proofs.Schnorr.AGMSecurity
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp AlgebraicGroupModel.Interaction Schnorr.AGM Schnorr.AGM.Reduction

namespace SignaturesTest.SchnorrAGMReduction

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev F := ZMod 7
noncomputable local instance : SampleableType F := SampleableType.ofFintype _

private def firstState : Reduction.State F F Unit :=
  record {} ((), 1) ⟨1, 0⟩ 2

-- These two valid representations describe the same commitment for secret three.
-- Only the second one has zero denominator after challenge two is known.
example : (Affine.mk (1 : F) 0).eval (1 : F) 3 =
    (Affine.mk (0 : F) 5).eval (1 : F) 3 := by decide
example : (Affine.mk (1 : F) 0).secret + 2 ≠ 0 := by decide
example : (Affine.mk (0 : F) 5).secret + 2 = 0 := by decide

-- A repeated hash must retain the first representation and the original bad flag.
example : (read ((), (1 : F)) ⟨0, 5⟩).run firstState = pure (2, firstState) := by
  simp [Reduction.read, StateT.run, firstState, record]

-- A colliding signing simulation also preserves the previous hash entry.
example : (signedState firstState 1 3 () 2 0).cache ((), 1) =
    some ⟨2, some ⟨1, 0⟩⟩ := by
  have hR : (0 : F) • (1 : F) - (2 : F) • (3 : F) = 1 := by decide
  simp only [signedState, hR]
  simp [firstState, record]

private def lateExplanation : Explained F (Unit × F) (Group F) :=
  ⟨⟨((), 0), fun _ => [1]⟩, fun _ => [[0, 5]]⟩

example : lateExplanation.Valid (representedBasis (1 : F) 3 firstState.representations) := by
  intro u
  fin_cases u
  norm_num [lateExplanation, representedBasis, firstState, record,
    initialRepresentations, Affine.eval, evaluate, smul_eq_mul]
  decide

-- Final extraction uses the first cached representation and recovers three.
-- Replacing it with the late explanation would divide by zero and return zero.
example : (finish (1 : F) 3 lateExplanation).run firstState =
    pure ((true, 3), firstState) := by
  simp only [finish, lateExplanation, StateT.run_bind, StateT.run_get,
    StateT.run_pure, pure_bind]
  norm_num [firstState, Reduction.read, record, StateT.run, smul_eq_mul]
  constructor
  · decide
  · apply (div_eq_iff (by decide : (2 : F) ≠ 0)).2
    decide

example : (signedState firstState 1 3 () 2 0).representations.length = 3 := by
  rfl

end SignaturesTest.SchnorrAGMReduction

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``Schnorr.AGM.flatten_eval, ``Schnorr.AGM.valid_singleton,
      ``Schnorr.AGM.Reduction.record_valid, ``Schnorr.AGM.Reduction.signedState_valid,
      ``Schnorr.AGM.Reduction.finish_sound, ``Schnorr.AGM.Reduction.simulate_valid,
      ``Schnorr.AGM.Reduction.run_extract, ``Schnorr.AGM.Reduction.run_bad,
      ``Schnorr.AGM.Reduction.simulated_security,
      ``Schnorr.AGM.Reduction.nonce_collision,
      ``Schnorr.AGM.Reduction.compare_observe,
      ``Schnorr.AGM.Reduction.honest_simulated,
      ``Schnorr.AGM.Reduction.Source.handler_erase,
      ``Schnorr.AGM.Reduction.Source.simulate_observe,
      ``Schnorr.AGM.Reduction.honestGame_eq,
      ``Schnorr.AGM.honestGame_dist, ``Schnorr.AGM.security] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
