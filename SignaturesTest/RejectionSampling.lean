import Proofs.Runtime.RejectionSampling
import Lean.Util.CollectAxioms

open Signatures.Runtime.RejectionSampling
open scoped ENNReal

namespace SignaturesTest.RejectionSampling

example : sample 5 3 3 none = (27 / 512 : ℝ≥0∞) := by
  rw [failure 5 3 3 (by decide)]
  apply (ENNReal.toNNReal_eq_toNNReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toNNReal_pow, ENNReal.toNNReal_sub,
    ENNReal.toNNReal_mul, ENNReal.toNNReal_inv, ENNReal.toNNReal_div,
    ENNReal.toNNReal_one, ENNReal.toNNReal_ofNat, ENNReal.toNNReal_natCast]
  apply Subtype.ext
  norm_num [NNReal.sub_def]

example (x : Fin 5) : sample 5 3 3 (some x) = (97 / 512 : ℝ≥0∞) := by
  simp only [sample_some_succ, draw_some 5 3 (by decide), draw_none 5 3 (by decide)]
  norm_num only [sample, PMF.pure_apply, reduceCtorEq, ite_false, mul_zero, add_zero]
  apply (ENNReal.toNNReal_eq_toNNReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toNNReal_add, ENNReal.toNNReal_sub,
    ENNReal.toNNReal_mul, ENNReal.toNNReal_inv, ENNReal.toNNReal_div,
    ENNReal.toNNReal_one, ENNReal.toNNReal_ofNat]
  apply Subtype.ext
  norm_num [NNReal.sub_def]

example : sample 4 2 1 none = 0 := by
  rw [failure 4 2 1 (by decide)]
  norm_num [ENNReal.mul_inv_cancel]

example : sample 1 0 1 (some 0) = 1 := by
  rw [sample_some_succ, draw_some 1 0 (by decide), draw_none 1 0 (by decide)]
  norm_num

example : sample 0 0 3 none = 1 := by
  rw [failure 0 0 3 (by decide)]
  norm_num

example : sample 5 3 0 none = 1 := by
  rw [failure 5 3 0 (by decide)]
  norm_num

-- Enumerate the full fair tape space: 27 failures and 97 copies of each output.
#eval show IO Unit from do
  let mut counts := Array.replicate 6 0
  for x in List.finRange 8 do
    for y in List.finRange 8 do
      for z in List.finRange 8 do
        let r := runTape 5 (w := 3) [x, y, z]
        let index := r.1.map Fin.val |>.getD 5
        counts := counts.modify index (· + 1)
        unless r.2 ≤ 3 do throw <| IO.userError "sampler consumed too many words"
  unless counts == #[97, 97, 97, 97, 97, 27] do
    throw <| IO.userError s!"sampler output counts: {counts}"
  unless (runTape 5 (w := 3) []).2 == 0 &&
      (runTape 5 (w := 3) [0, 7, 7]).2 == 1 &&
      (runTape 5 (w := 3) [7, 7, 4]).2 == 3 do
    throw <| IO.userError "sampler stopping count mismatch"

end SignaturesTest.RejectionSampling

open Lean Meta Elab Command in
run_cmd liftTermElabM do
  for name in #[``fairWord_uniform, ``fairSample_eq, ``draw_some,
      ``Signatures.Runtime.RejectionSampling.failure,
      ``sample_uniform, ``sample_some, ``runTape_steps, ``runTape_bits, ``runTape_distribution,
      ``runTape_failure, ``fairTape_bit_budget, ``failure_le_half, ``failure_size] do
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains) do
      throwError "{name}: unexpected axiom footprint {axioms}"
