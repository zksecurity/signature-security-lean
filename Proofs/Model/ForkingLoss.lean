import Proofs.Model.Hardness
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! A direct forgery-probability bound from the usual quadratic forking
inequality. Subtraction in the premise is truncated ENNReal subtraction. -/

namespace Model

theorem forking_inverse {p loss inverse epsilon : ENNReal} (q : Nat)
    (hp : p ≠ ⊤) (hi : inverse ≠ ⊤)
    (h : (p - loss) * ((p - loss) / (q + 1 : ENNReal) - inverse) ≤ epsilon) :
    p ≤ loss + (q + 1 : ENNReal) * inverse + ((q + 1 : ENNReal) * epsilon) ^ (1 / 2 : ℝ) := by
  have hq : (q + 1 : ENNReal) ≠ 0 := by positivity
  by_cases ht : epsilon = ⊤
  · simp [ht, ENNReal.mul_top hq]
  have he : p - loss ≠ ⊤ := ne_top_of_le_ne_top hp tsub_le_self
  have hd : (p - loss) / (q + 1 : ENNReal) ≠ ⊤ := ENNReal.div_ne_top he hq
  have hs : (p - loss) / (q + 1 : ENNReal) - inverse ≠ ⊤ := ne_top_of_le_ne_top hd tsub_le_self
  have hf : (q + 1 : ENNReal) ≠ ⊤ := by finiteness
  have hr : ((q + 1 : ENNReal) * epsilon) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.mul_ne_top hf ht)
  have hreal := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top he hs) ht).mpr h
  rw [ENNReal.toReal_mul] at hreal
  have hsub := ENNReal.le_toReal_sub hi (a := (p - loss) / (q + 1 : ENNReal))
  have hineq := (mul_le_mul_of_nonneg_left hsub (show 0 ≤ (p - loss).toReal from ENNReal.toReal_nonneg)).trans hreal
  rw [ENNReal.toReal_div] at hineq
  let N := (q + 1 : ENNReal).toReal
  let e := (p - loss).toReal
  let i := inverse.toReal
  let E := epsilon.toReal
  have hN : 0 < N := ENNReal.toReal_pos hq hf
  have hpoly : e * e - N * i * e ≤ N * E := by
    have hmul := mul_le_mul_of_nonneg_left hineq hN.le
    change N * (e * (e / N - i)) ≤ N * E at hmul
    have eqn : N * (e * (e / N - i)) = e * e - N * i * e := by
      field_simp [hN.ne']
    rwa [eqn] at hmul
  have hroot : Real.sqrt (N * E) ^ 2 = N * E := Real.sq_sqrt (mul_nonneg hN.le ENNReal.toReal_nonneg)
  have hbound : e ≤ N * i + Real.sqrt (N * E) := by
    have he0 : 0 ≤ e := ENNReal.toReal_nonneg
    have hi0 : 0 ≤ i := ENNReal.toReal_nonneg
    have hr0 := Real.sqrt_nonneg (N * E)
    have hni : 0 ≤ N * i := mul_nonneg hN.le hi0
    nlinarith
  have hencoded : p - loss ≤ (q + 1 : ENNReal) * inverse + ((q + 1 : ENNReal) * epsilon) ^ (1 / 2 : ℝ) := by
    apply (ENNReal.toReal_le_toReal he (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hf hi, hr⟩)).mp
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top hf hi) hr, ENNReal.toReal_mul,
      ← ENNReal.toReal_rpow, ENNReal.toReal_mul, ← Real.sqrt_eq_rpow]
    exact hbound
  calc
    p ≤ (p - loss) + loss := le_tsub_add
    _ ≤ ((q + 1 : ENNReal) * inverse + ((q + 1 : ENNReal) * epsilon) ^ (1 / 2 : ℝ)) + loss :=
      add_le_add hencoded le_rfl
    _ = _ := by ac_rfl

end Model
