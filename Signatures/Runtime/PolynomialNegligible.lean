import Signatures.Runtime.PolynomialResources
import VCVio.CryptoFoundations.Asymptotics.Negligible

/-! Connect the fixed-polynomial resource convention to VCVio's standard
superpolynomial-decay notion of negligible advantage. -/

namespace Signatures.Runtime

open Complexity

theorem negligible_polynomial_eval_mul (p : FirstOrderPolynomial) {epsilon : Nat → ENNReal}
    (he : negligible epsilon) : negligible (fun n => (p.eval n : ENNReal) * epsilon n) := by
  induction p generalizing epsilon with
  | const value => exact negligible_const_mul he (ENNReal.natCast_ne_top value)
  | input => simpa only [pow_one, FirstOrderPolynomial.eval, SecondOrderPolynomial.eval_input] using negligible_pow_mul he 1
  | add p q hp hq =>
      have h := negligible_add (hp he) (hq he)
      have heq : (fun n => (FirstOrderPolynomial.eval (SecondOrderPolynomial.add p q) n : ENNReal) * epsilon n) =
          ((fun n => (FirstOrderPolynomial.eval p n : ENNReal) * epsilon n) +
            fun n => (FirstOrderPolynomial.eval q n : ENNReal) * epsilon n) := by
        funext n
        simp only [FirstOrderPolynomial.eval, SecondOrderPolynomial.eval_add, Nat.cast_add, add_mul, Pi.add_apply]
      rw [heq]
      exact h
  | mul p q hp hq =>
      simpa only [FirstOrderPolynomial.eval, SecondOrderPolynomial.eval_mul, Nat.cast_mul, mul_assoc]
        using hp (hq he)
  | oracle symbol argument ih => exact symbol.elim

theorem PolynomiallyBounded.negligible_mul {resource : Nat → Nat}
    (hr : PolynomiallyBounded resource) {epsilon : Nat → ENNReal} (he : negligible epsilon) :
    negligible (fun n => (resource n : ENNReal) * epsilon n) := by
  obtain ⟨p, hp⟩ := hr
  apply negligible_of_le _ (negligible_polynomial_eval_mul p he)
  intro n
  exact mul_le_mul' (by exact_mod_cast hp n) le_rfl

end Signatures.Runtime
