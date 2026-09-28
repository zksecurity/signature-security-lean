import Signatures.Runtime.ProximityWeight
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime

namespace SignaturesTest.RuntimeTuple

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private def cost := PrimitiveCosts.unit
private def primitives := arithmetic F F F Bool Unit cost
private def vector : (tupleTy scalar 3).Value (cryptoBase F F F Bool Unit) := (2, 3, 4, ())

example : (tupleIndex 0).run primitives (42, (), ()) = ⟨0, 3⟩ := rfl
example : (tupleIndex 3).run primitives (0, vector, ()) = ⟨2, 9⟩ := rfl
example : ((tupleIndex 3).run primitives (2, vector, ())).value = (4 : F) := rfl
example : ((tupleIndex 3).run primitives (3, vector, ())).value = (0 : F) := rfl

example (n k : Nat) (x : (tupleTy scalar n).Value (cryptoBase F F F Bool Unit)) :
    ((tupleIndex n).run primitives (k, x, ())).steps ≤ 18 * n + 3 := by
  simpa [primitives, tupleIndexBound, cost, PrimitiveCosts.unit, Nat.mul_comm, Nat.add_assoc] using
    tupleIndex_steps_le (G₁ := F) (G₂ := F) (K := Bool) (M := Unit) cost n k x

example (n : Nat) (x : (tupleTy scalar n).Value (cryptoBase F F F Bool Unit)) :
    (Ty.load (tupleTy scalar n) x).steps = 2 * n + 1 := tupleScalar_load_steps n x

example : (Weights.proximityTuple 0).run primitives ((0, false), ((), false), ()) =
    ⟨1, 21⟩ := rfl
example : (Weights.proximityTuple 3).run primitives ((0, false), (vector, false), ()) =
    ⟨1, 21⟩ := rfl
example : (Weights.proximityTuple 3).run primitives ((3, false), (vector, true), ()) =
    ⟨0, 12⟩ := rfl
example : ((Weights.proximityTuple 3).run primitives ((1, false), (vector, false), ())).value =
    (2 : F) := rfl
example : ((Weights.proximityTuple 3).run primitives ((2, false), (vector, false), ())).value =
    (3 : F) := rfl
example : ((Weights.proximityTuple 3).run primitives ((3, false), (vector, false), ())).value =
    (4 : F) := rfl

-- Every typed message is well formed; the runtime premise has no length restriction.
example (n : Nat) (i : Fin (n + 1) × Bool)
    (m : (Weights.proximityTupleMessage n).Value (cryptoBase F F F Bool Unit)) :
    ((Weights.proximityTuple n).run primitives (i, m, ())).steps ≤ 18 * n + 36 := by
  simpa [primitives, Weights.proximityTupleBound, tupleIndexBound, cost, PrimitiveCosts.unit,
    Nat.mul_comm, Nat.add_assoc] using
    Weights.proximityTuple_steps_le (G₁ := F) (G₂ := F) (M := Unit) cost n i m

example (n : Nat) (f : Fin n → F) (i : Fin n) :
    ((Weights.proximityTuple n).run primitives
      (Weights.encodeProximityKey (some i, false),
        (Tuple.encode (cell := scalar) (base := cryptoBase F F F Bool Unit) n f, false), ())).value = f i := by
  have h := Weights.proximityTuple_native (G₁ := F) (G₂ := F) (M := Unit) cost n
    (some i, false) (Tuple.encode n f, false)
  simpa [primitives, Weights.proximityMessageEquiv, Tuple.equiv, Tuple.decode_encode,
    Proximity.Proofs.coordinateWeight] using h

end SignaturesTest.RuntimeTuple

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Tuple.decode_encode, ``Tuple.encode_decode,
      ``tupleIndex_value, ``tupleIndex_steps_le, ``tupleScalar_load_steps,
      ``Weights.decodeProximityKey_encode, ``Weights.encodeProximityKey_decode,
      ``Weights.proximityTuple_native, ``Weights.proximityTuple_steps_le,
      ``Weights.proximityTuple_decoded] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
