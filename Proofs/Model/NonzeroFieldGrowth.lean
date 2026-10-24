import Proofs.Runtime.PolynomialNegligible
import Mathlib.Data.Fintype.EquivFin

/-! Excluding zero changes inverse field size by at most a factor of two.
The nonzero-nonce family theorem therefore needs no stronger field-growth
assumption than the full-field theorem. -/

namespace Model

theorem inv_pred_le_twice_inv (size : Nat) (hsize : 2 ≤ size) :
    ((size - 1 : Nat) : ENNReal)⁻¹ ≤ 2 * (size : ENNReal)⁻¹ := by
  have h : (size : ENNReal) ≤ 2 * ((size - 1 : Nat) : ENNReal) := by
    exact_mod_cast (show size ≤ 2 * (size - 1) by omega)
  have hm := mul_le_mul' (le_refl (2 : ENNReal)) (ENNReal.inv_le_inv.mpr h)
  rw [ENNReal.mul_inv (a := 2) (b := ((size - 1 : Nat) : ENNReal))
    (Or.inl (by norm_num)) (Or.inl (by simp))] at hm
  simpa only [ENNReal.mul_inv_cancel_left (by norm_num : (2 : ENNReal) ≠ 0)
    (by simp : (2 : ENNReal) ≠ ⊤)] using hm

theorem negligible_inv_pred {size : Nat → Nat} (hsize : ∀ n, 2 ≤ size n)
    (growth : negligible (fun n => (size n : ENNReal)⁻¹)) :
    negligible (fun n => ((size n - 1 : Nat) : ENNReal)⁻¹) :=
  negligible_of_le (fun n => inv_pred_le_twice_inv (size n) (hsize n))
    (negligible_const_mul growth (by simp : (2 : ENNReal) ≠ ⊤))

theorem negligible_inv_card_sub_one {F : Nat → Type} [∀ n, Fintype (F n)] [∀ n, Nontrivial (F n)]
    (growth : negligible (fun n => (Fintype.card (F n) : ENNReal)⁻¹)) :
    negligible (fun n => ((Fintype.card (F n) - 1 : Nat) : ENNReal)⁻¹) :=
  negligible_inv_pred (fun n => show 2 ≤ Fintype.card (F n) from Fintype.one_lt_card) growth

end Model
