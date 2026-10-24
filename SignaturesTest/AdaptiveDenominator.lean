import Mathlib.Algebra.Field.ZMod
import Proofs.AlgebraicGroupModel.ForgeryGame

/-!
# Adaptive zero-denominator regression

Finite algebra and counting checks for the review's degree-one example. These checks do not
formalize the probability bridge to the full OOPS experiment; they pin down the root selection,
zero extractor, and counts used in that argument without importing an admitted security theorem.
-/

namespace SignaturesTest.AdaptiveDenominator

open OracleComp

abbrev F := ZMod 5

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def rootMessage (h0 h1 : F) : F := -h0 / h1

example (h0 h1 : F) (hne : h1 ≠ 0) : h0 + rootMessage h0 h1 * h1 = 0 := by
  simp [rootMessage, div_mul_cancel₀ _ hne]

-- A zero representation always makes the division-only extractor return zero.
example (denominator : F) : (0 : F) / denominator = 0 := zero_div _

def accepts (x : F × F × F) : Prop :=
  x.1 * (x.2.1 + rootMessage x.2.1 x.2.2 * x.2.2) = 0

instance (x : F × F × F) : Decidable (accepts x) := inferInstanceAs (Decidable (_ = _))

set_option maxRecDepth 4096 in
example : (Finset.univ.filter accepts).card = 109 := by decide +kernel

example : (Finset.univ.filter (fun x : F => x = 0)).card = 1 := by decide

example : (109 : ℚ) / 125 > 1 / 5 + 1 / 5 := by norm_num

-- The collision kernel needs a nonzero slope: one root versus every field element.
example : Pr[fun ρ : F => 2 * ρ + 3 = 4 | ($ᵗ F : ProbComp F)] = 1 / 5 := by
  rw [probEvent_uniformSample]
  have hcard : (Finset.univ.filter (fun ρ : F => 2 * ρ + 3 = 4)).card = 1 := by decide
  rw [hcard]
  norm_num [F]

example : Pr[fun ρ : F => 0 * ρ + 3 = 3 | ($ᵗ F : ProbComp F)] = 1 := by simp

end SignaturesTest.AdaptiveDenominator
