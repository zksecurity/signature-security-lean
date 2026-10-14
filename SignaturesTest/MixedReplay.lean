import Signatures.Runtime.MixedReplay
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.Replay.Mixed

namespace SignaturesTest.MixedReplay

private abbrev F := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def primitives := arithmetic F F F Unit Unit PrimitiveCosts.unit
private def sampling : Machine.SamplingCosts := ⟨11, fun _ => 7⟩

-- Zero is replayed as a scalar, and the live/private tag is retained in the new log.
example : (fun z => (z.1.value, z.2)) <$>
    (((scalarDraw false).run primitives (Machine.effects sampling store) ((), ())).run
      (0, 1, [(0, (0 : F), 0)], [])) =
      pure ((0 : F), (1, 1, [(0, (0 : F), 0)], [(0, (0 : F), 0)])) := by
  refine (draw_erase (F := F) (G₁ := F) (G₂ := F) (K := Unit) (M := Unit)
      PrimitiveCosts.unit sampling 1 1 .scalar scalarDecode (scalarEncode false)
      ($ᵗ F) sampling.scalar (fun _ => rfl) 0 1 [(0, (0 : F), 0)] []).trans ?_
  rfl

-- Finite replies are stored as naturals and decoded back to their precise result type.
example : (fun z => (z.1.value, z.2)) <$>
    (((uniformDraw 3).run primitives (Machine.effects sampling store) ((), ())).run
      (0, 1, [(5, (0 : F), 3)], [])) =
      pure ((3 : Fin 4), (1, 1, [(5, (0 : F), 3)], [(5, (0 : F), 3)])) := by
  refine (draw_erase (F := F) (G₁ := F) (G₂ := F) (K := Unit) (M := Unit)
      PrimitiveCosts.unit sampling 1 1 (.uniform 3) (uniformDecode 3) (uniformEncode 3)
      (liftM (unifSpec.query 3)) (sampling.uniform 3) (fun _ => rfl)
      0 1 [(5, (0 : F), 3)] []).trans ?_
  rfl

-- At the prefix boundary a live challenge is fresh, not copied from the last cell.
-- Its exact charge includes the encoder, two natural operations and the draw itself.
example : (((scalarDraw true).run primitives (Machine.effects sampling store) ((), ())).run
    (1, 1, [(0, (0 : F), 0)], [])) =
      (fun answer : F => (⟨answer, 78⟩,
        (2, 1, [(0, (0 : F), 0)], [(1, answer, 0)]))) <$> ($ᵗ F : ProbComp F) := by
  exact draw_miss PrimitiveCosts.unit sampling 1 1 .scalar scalarDecode (scalarEncode true)
    ($ᵗ F) sampling.scalar (fun _ => rfl) 1 1 [(0, (0 : F), 0)] [] (by decide)

-- Fin 1 has only zero, including when total decoding is given an arbitrary natural.
example : (uniformDecode 0).denote primitives ((2, (0 : F), 19), ()) = (0 : Fin 1) := by
  apply Fin.ext
  exact Nat.mod_one _

end SignaturesTest.MixedReplay

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``draw_hit, ``draw_miss, ``draw_erase, ``draw_bound,
      ``scalarDraw_bound, ``uniformDraw_bound, ``uniformCodec_roundtrip] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
