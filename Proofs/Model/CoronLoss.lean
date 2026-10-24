import Signatures.Model.CoCDH
import Proofs.Runtime.PolynomialNegligible
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The exact Coron loss is at most a linear factor, including the zero-signing
case. Polynomial signing bounds therefore preserve negligible advantage. -/

namespace Model

theorem coronFactor_le (qS : Nat) : coronFactor qS ≤ 3 * (qS + 1 : ENNReal) := by
  by_cases hzero : qS = 0
  · subst qS
    norm_num [coronFactor]
  have hq : (0 : ℝ) < qS := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hstep : ((qS : ℝ) + 1) / qS ≤ Real.exp (1 / qS) := by
    have he := Real.add_one_le_exp (1 / (qS : ℝ))
    have hratio : ((qS : ℝ) + 1) / qS = 1 / qS + 1 := by field_simp; ring
    rwa [hratio]
  have hp : (((qS : ℝ) + 1) / qS) ^ qS ≤ Real.exp 1 := by
    have hn := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((qS : ℝ) + 1) / qS) hstep qS
    rw [← Real.exp_nat_mul] at hn
    simpa [hq.ne'] using hn
  have hfinite : coronFactor qS ≠ ⊤ := by
    simp [coronFactor, hzero]
  apply (ENNReal.toReal_le_toReal hfinite (by finiteness)).mp
  have hloss : (coronFactor qS).toReal = ((qS : ℝ) + 1) * (((qS : ℝ) + 1) / qS) ^ qS := by
    simp [coronFactor, ENNReal.toReal_add, ← inv_pow, inv_div, mul_comm]
  rw [hloss]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.toReal_add (ENNReal.natCast_ne_top qS) ENNReal.one_ne_top,
    ENNReal.toReal_natCast, ENNReal.toReal_one]
  nlinarith [Real.exp_one_lt_three]

theorem negligible_of_coron_bound {advantage epsilon : Nat → ENNReal} {qS : Nat → Nat}
    (hq : Signatures.Runtime.PolynomiallyBounded qS) (he : negligible epsilon)
    (hbound : ∀ n, advantage n ≤ coronFactor (qS n) * epsilon n) : negligible advantage := by
  have hp := (Signatures.Runtime.PolynomiallyBounded.const 3).mul
    (hq.add (Signatures.Runtime.PolynomiallyBounded.const 1))
  apply negligible_of_le _ (hp.negligible_mul he)
  intro n
  refine (hbound n).trans ?_
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
    mul_le_mul' (coronFactor_le (qS n)) (le_refl (epsilon n))

end Model
