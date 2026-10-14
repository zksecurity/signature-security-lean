import PolyFun.Realizability.Quantitative.Polynomial
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Polynomial resource families use one fixed polynomial across the security
parameter. The joint structural-overhead contract also bounds the sizes supplied
at runtime. These are numerical closure facts, separate from executable
realization, uniformity, and cryptographic hardness. -/

namespace Signatures.Runtime

open Complexity

def PolynomiallyBounded (resource : Nat → Nat) : Prop :=
  ∃ polynomial : FirstOrderPolynomial, ∀ n, resource n ≤ polynomial.eval n

namespace PolynomiallyBounded

theorem const (value : Nat) : PolynomiallyBounded (fun _ => value) :=
  ⟨.const value, fun _ => le_rfl⟩

theorem input : PolynomiallyBounded id := ⟨.input, fun _ => le_rfl⟩

theorem of_le {f g : Nat → Nat} (hg : PolynomiallyBounded g) (h : ∀ n, f n ≤ g n) :
    PolynomiallyBounded f := by
  obtain ⟨p, hp⟩ := hg
  exact ⟨p, fun n => (h n).trans (hp n)⟩

theorem add {f g : Nat → Nat} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n + g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨.add p q, fun n => Nat.add_le_add (hp n) (hq n)⟩

theorem mul {f g : Nat → Nat} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  exact ⟨.mul p q, fun n => Nat.mul_le_mul (hp n) (hq n)⟩

theorem comp {f g : Nat → Nat} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f (g n)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p.comp q, fun n => ?_⟩
  rw [FirstOrderPolynomial.eval_comp]
  exact (hp (g n)).trans (p.eval_monotone (hq n))

theorem sum {K : Type} [Fintype K] (f : K → Nat → Nat)
    (hf : ∀ k, PolynomiallyBounded (f k)) : PolynomiallyBounded (fun n => ∑ k, f k n) := by
  classical
  have hs : ∀ s : Finset K, PolynomiallyBounded (fun n => s.sum (fun k => f k n)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using const 0
    | @insert k s hk ih => simpa only [Finset.sum_insert hk] using (hf k).add ih
  exact hs Finset.univ

end PolynomiallyBounded

/-- A single polynomial controls overhead jointly in the security parameter
and encoded frame size. Allowing an arbitrary degree at each parameter would
not be a polynomial-family guarantee. -/
def PolynomialOverhead (overhead : Nat → Nat → Nat) : Prop :=
  ∃ polynomial : FirstOrderPolynomial, ∀ parameter size,
    overhead parameter size ≤ polynomial.eval (parameter + size)

theorem PolynomialOverhead.apply {overhead : Nat → Nat → Nat}
    (h : PolynomialOverhead overhead) {size : Nat → Nat} (hs : PolynomiallyBounded size) :
    PolynomiallyBounded (fun n => overhead n (size n)) := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := hs
  refine ⟨p.comp (.add .input q), fun n => ?_⟩
  rw [FirstOrderPolynomial.eval_comp]
  exact (hp n (size n)).trans (p.eval_monotone (Nat.add_le_add_left (hq n) n))

end Signatures.Runtime
