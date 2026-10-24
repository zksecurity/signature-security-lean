import Proofs.Runtime.PaddedSampling
import Proofs.Runtime.MarkedProbability

/-! The fair-bit sampler is ideal uniform on its unmarked mass, scaled by the
acceptance probability. These are laws of the existing executable sampler,
not an assumed approximate sampling interface. -/

namespace Signatures.Runtime.RejectionSampling

open scoped ENNReal

theorem marked_good_le (n w k : Nat) [NeZero n] (hfit : n ≤ 2^w) (fallback : Fin n) :
    MarkedProbability.GoodLe
      ((sample n w k).map (fun x => (x.getD fallback, x.isNone))) (PMF.uniformOfFintype (Fin n)) := by
  classical
  intro x
  have he : ((sample n w k).map (fun x => (x.getD fallback, x.isNone))) (x, false) =
      sample n w k (some x) := by
    simp [PMF.map_apply, tsum_fintype, Fintype.sum_option, Prod.ext_iff]
  rw [he, sample_some n w k hfit, PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [div_eq_mul_inv]
  simpa only [one_mul] using
    (mul_le_mul' (tsub_le_self : 1-(1-n*(2^w : ℝ≥0∞)⁻¹)^k ≤ 1) (le_refl (n : ℝ≥0∞)⁻¹))

end Signatures.Runtime.RejectionSampling

namespace Signatures.Runtime.PaddedSampling

open PrimeFieldCircuit SharedHeap OracleComp
open scoped ENNReal

/-- Semantic decoding for the probability proof; the executable sampler
continues to return a word and a flag without this decoder. -/
noncomputable def decoded (n w k : Nat) [NeZero n] : PMF (Fin n × Bool) :=
  (simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (run (compile n w k))).map
    (fun out => (Fin.ofNat n (exponent out.value.1), out.value.2))

theorem decoded_distribution (n w k : Nat) [NeZero n] (hfit : n ≤ 2^w) :
    decoded n w k = (RejectionSampling.sample n (width n w) k).map (fun x => (x.getD 0, x.isNone)) := by
  let p := simulateQ (fun _ : Unit => PMF.uniformOfFintype Bool) (run (compile n w k))
  have h := PMF.map_comp (Run.value : Run (List Bool × Bool) → List Bool × Bool) p
    (fun x => (Fin.ofNat n (exponent x.1), x.2))
  dsimp only [Function.comp_def, p] at h
  change decoded n w k = _
  rw [decoded, ← h, distribution n w k hfit, PMF.map_comp]
  congr 1
  funext x
  cases x with
  | none =>
    change (Fin.ofNat n (exponent (natBits w 0)), true) = (0, true)
    rw [HeapLoop.exponent_natBits _ _ (by positivity)]
    rfl
  | some x =>
    change (Fin.ofNat n (exponent (natBits w x.val)), false) = (x, false)
    rw [HeapLoop.exponent_natBits _ _ (x.isLt.trans_le hfit)]
    exact congrArg (fun a : Fin n => (a, false)) (Fin.ext (Nat.mod_eq_of_lt x.isLt))

theorem decoded_good_le (n w k : Nat) [NeZero n] (hfit : n ≤ 2^w) :
    MarkedProbability.GoodLe (decoded n w k) (PMF.uniformOfFintype (Fin n)) := by
  rw [decoded_distribution n w k hfit]
  exact RejectionSampling.marked_good_le n (width n w) k (fits n w hfit) 0

theorem decoded_bad_le (n w k : Nat) [NeZero n] (hfit : n ≤ 2^w) :
    MarkedProbability.bad (decoded n w k) ≤ (1/2 : ℝ≥0∞)^k := by
  rw [MarkedProbability.bad_eq_map, decoded, PMF.map_comp]
  exact bad_le n w k (NeZero.pos n) hfit

end Signatures.Runtime.PaddedSampling
