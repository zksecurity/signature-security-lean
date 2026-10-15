import Signatures.Model.ForkingLoss
import Signatures.Runtime.PolynomialNegligible
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Polynomial query losses and a square root preserve negligible advantage.
This closes the asymptotic step for the concrete quadratic forking bound. -/

namespace Model

theorem negligible_sqrt {f : Nat → ENNReal} (hf : negligible f) :
    negligible (fun n => f n ^ (1 / 2 : ℝ)) := by
  intro k
  have h := (hf (k * 2)).ennrpow_const (1 / 2 : ℝ)
  rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  change (((n : ENNReal) ^ (k * 2)) * f n) ^ (1 / 2 : ℝ) = (n : ENNReal) ^ k * f n ^ (1 / 2 : ℝ)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  rw [pow_mul, one_div]
  exact ENNReal.pow_rpow_inv_natCast (by decide : (2 : Nat) ≠ 0) _

theorem negligible_of_forking_bound {p loss inverse epsilon : Nat → ENNReal} {q : Nat → Nat}
    (hp : ∀ n, p n ≠ ⊤) (hi : ∀ n, inverse n ≠ ⊤)
    (hQ : Signatures.Runtime.PolynomiallyBounded q)
    (hLoss : negligible loss) (hInverse : negligible inverse) (hEpsilon : negligible epsilon)
    (h : ∀ n, (p n - loss n) * ((p n - loss n) / (q n + 1 : ENNReal) - inverse n) ≤ epsilon n) :
    negligible p := by
  have hNext := hQ.add (Signatures.Runtime.PolynomiallyBounded.const 1)
  have hInv : negligible (fun n => (q n + 1 : ENNReal) * inverse n) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hNext.negligible_mul hInverse
  have hRoot : negligible (fun n => ((q n + 1 : ENNReal) * epsilon n) ^ (1 / 2 : ℝ)) := by
    apply negligible_sqrt
    simpa only [Nat.cast_add, Nat.cast_one] using hNext.negligible_mul hEpsilon
  exact negligible_of_le (fun n => forking_inverse (q n) (hp n) (hi n) (h n))
    (negligible_add (negligible_add hLoss hInv) hRoot)

end Model
