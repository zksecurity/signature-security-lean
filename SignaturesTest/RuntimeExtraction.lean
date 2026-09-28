import Signatures.Runtime.Extraction
import Signatures.Runtime.KeyEquality
import Signatures.Runtime.Weights
import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

open Signatures.Runtime

namespace SignaturesTest.RuntimeExtraction

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5
private def cost := PrimitiveCosts.unit
private abbrev primitives := arithmetic F F F Bool Unit cost
private def hashes : List (Bool × F) := [(false, 0), (true, 4), (false, 1)]
private def hrows : List ((Bool × F) × F) := [((false, 1), 1), ((true, 4), 2), ((false, 0), 3)]
private def srows : List ((Bool × F) × F) := [((false, 2), 1), ((true, 3), 1)]
private def rho : List (Bool × F) := [(false, 2), (true, 3)]

-- Coefficients follow chronological replies, including duplicate keys and zero replies.
example : ((AGM.tokenRows (dataTy := key)).run primitives (hashes, [1, 2, 3], ())).value = hrows := by
  rw [AGM.tokenRows_value]
  rfl

example : ((AGM.tokenRows (dataTy := key)).run primitives (hashes, [2], ())).value =
    [((false, 1), 2), ((true, 4), 0), ((false, 0), 0)] := by
  rw [AGM.tokenRows_value]
  rfl

example : ((AGM.tokenRows (dataTy := key)).run primitives ([], [1, 2, 3], ())).value = [] := by
  rw [AGM.tokenRows_value]
  rfl

example (tr : List (Bool × F)) (coeff : List F) :
    ((AGM.tokenRows (dataTy := key)).run primitives (tr, coeff, ())).steps ≤
      tr.length * (28 * coeff.length + 71) + 30 := by
  have h := AGM.tokenRows_steps_le (dataTy := key) (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
    cost tr coeff
  change _ ≤ tr.length * (coeff.length * 28 + 71) + 30 at h
  nlinarith

example : ((AGM.baseCoefficient AGM.KeyEquality.bls).run primitives (false, hrows, ())).value =
    (4 : F) := by
  rw [AGM.baseCoefficient_value cost AGM.KeyEquality.bls (fun x y => AGM.KeyEquality.bls_value cost x y)]
  rfl

example : ((AGM.denominatorWeight Weights.bls).run primitives (false, (false, srows), ())).value =
    (0 : F) := by
  rw [AGM.denominatorWeight_value]
  rfl

example : ((AGM.denominatorWeight Weights.bls).run primitives (true, (false, srows), ())).value =
    (4 : F) := by
  rw [AGM.denominatorWeight_value]
  rfl

example (i m : Bool) (xs : List ((Bool × F) × F)) :
    ((AGM.denominatorWeight Weights.bls).run primitives (i, (m, xs), ())).steps ≤
      xs.length * 46 + 47 := by
  exact AGM.denominatorWeight_steps_le cost Weights.bls 10
    (fun i m => le_of_eq (Weights.bls_steps cost i m)) i m xs

private theorem goodValue : ((AGM.goodCore AGM.KeyEquality.bls Weights.bls).run primitives
    (rho, 2, hrows, (false, srows), ())).value = (3 : F) := by
  rw [AGM.goodCore_run]
  change (1 : F) / 2 = 3
  apply (div_eq_iff (by decide : (2 : F) ≠ 0)).2
  decide

private theorem badValue : ((AGM.badCore Weights.bls).run primitives
    (rho, [(false, 4), (true, 2)], (false, srows), ())).value = (1 : F) := by
  rw [AGM.badCore_run]
  change -(3 : F) / 2 = 1
  apply (div_eq_iff (by decide : (2 : F) ≠ 0)).2
  decide

example : ((AGM.goodCore AGM.KeyEquality.bls Weights.bls).run primitives
    (rho, 2, hrows, (false, srows), ())).steps ≤ 730 := by
  exact AGM.goodCore_steps_le (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
    cost AGM.KeyEquality.bls Weights.bls 6 10
    (fun x y => le_of_eq (AGM.KeyEquality.bls_steps cost x y))
    (fun i m => le_of_eq (Weights.bls_steps cost i m)) rho 2 hrows (false, srows)

example : ((AGM.badCore Weights.bls).run primitives
    (rho, [(false, 4), (true, 2)], (false, srows), ())).steps ≤ 713 := by
  exact AGM.badCore_steps_le cost Weights.bls 10
    (fun i m => le_of_eq (Weights.bls_steps cost i m)) rho [(false, 4), (true, 2)] (false, srows)

private def out : (AGM.outputTy key).Value (cryptoBase F F F Bool Unit) := (false, 2, [1, 2, 3], [1, 1])
private def tr : (AGM.transcriptTy key key).Value (cryptoBase F F F Bool Unit) :=
  (hashes, [(true, 3), (false, 2)])

example : ((AGM.goodExtract AGM.KeyEquality.bls Weights.bls).run primitives (out, tr, rho, ())).value =
    (3 : F) := by
  rw [AGM.goodExtract_value]
  exact goodValue

example : ((AGM.badExtract Weights.bls).run primitives
    (out, tr, rho, [(false, 4), (true, 2)], ())).value = (1 : F) := by
  rw [AGM.badExtract_value]
  exact badValue

example : ((AGM.goodExtract AGM.KeyEquality.bls Weights.bls).run primitives
    (out, tr, rho, ())).steps ≤ 1555 := by
  exact AGM.goodExtract_steps_le (G₁ := F) (G₂ := F) (K := Bool) (M := Unit)
    cost AGM.KeyEquality.bls Weights.bls 6 10
    (fun x y => le_of_eq (AGM.KeyEquality.bls_steps cost x y))
    (fun i m => le_of_eq (Weights.bls_steps cost i m)) out tr rho

example : ((AGM.badExtract Weights.bls).run primitives
    (out, tr, rho, [(false, 4), (true, 2)], ())).steps ≤ 1023 := by
  exact AGM.badExtract_steps_le cost Weights.bls 10
    (fun i m => le_of_eq (Weights.bls_steps cost i m)) out tr rho [(false, 4), (true, 2)]

-- Division at zero is the same total field operation used by the native reduction.
example : ((AGM.goodExtract AGM.KeyEquality.bls Weights.bls).run primitives
    (out, ([], []), [], ())).value = (0 : F) := by
  rw [AGM.goodExtract_value, AGM.goodCore_run]
  change (2 : F) / 0 = 0
  exact div_zero _

example : ((AGM.badExtract Weights.bls).run primitives
    (out, ([], []), [], [], ())).value = (0 : F) := by
  rw [AGM.badExtract_value, AGM.badCore_run]
  change -(0 : F) / 0 = 0
  exact div_zero _

end SignaturesTest.RuntimeExtraction

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``AGM.tokenRows_run, ``AGM.tokenRows_value, ``AGM.tokenRows_steps_le,
      ``AGM.tokenRows_length, ``AGM.tokenWeight_run, ``AGM.baseIndicator_run,
      ``AGM.denominatorWeight_run, ``AGM.denominatorWeight_steps_le,
      ``AGM.baseCoefficient_value, ``AGM.baseCoefficient_steps_le,
      ``AGM.denominatorWeight_value, ``AGM.baseCoefficient_native, ``AGM.denominatorWeight_native,
      ``AGM.goodCore_run, ``AGM.badCore_run, ``AGM.goodCore_steps_le, ``AGM.badCore_steps_le,
      ``AGM.weighted_denominator_sum, ``AGM.goodCore_native, ``AGM.badCore_native,
      ``AGM.signingData_run, ``AGM.hashData_run, ``AGM.goodExtract_run, ``AGM.badExtract_run,
      ``AGM.goodExtract_value, ``AGM.badExtract_value, ``AGM.goodExtract_steps_le,
      ``AGM.badExtract_steps_le] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
