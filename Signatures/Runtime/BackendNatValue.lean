import Signatures.Runtime.BackendDataSize
import Mathlib.Data.Nat.Size

/-! A natural's numeric range is recovered from its encoded size. Binary
encodings permit exponential numeric values with linear bit width. Neither
this recovery law nor the Schnorr handler budget enumerates that numeric range. -/

open PFunctor

namespace Signatures.Runtime.BackendProgram

universe v w

variable {C : StepClass.{0, v}} {Q : QuantitativeStepClass.{0, v, w} C}

structure NatValueLaws (Q : QuantitativeStepClass.{0, v, w} C)
    (data : DataRepresentation C) where
  capacity : Nat → Nat
  monotone : Monotone capacity
  value_le : ∀ n, n ≤ capacity (Q.size data.nat n)

namespace NatValueLaws

variable {data : DataRepresentation C}

def binary (encoded : ∀ n, Nat.size n ≤ Q.size data.nat n) : NatValueLaws Q data where
  capacity bits := 2 ^ bits - 1
  monotone := fun _ _ h => Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) h) 1
  value_le n := by
    have h := (Nat.lt_size_self n).trans_le (Nat.pow_le_pow_right (by decide) (encoded n))
    omega

/-- The entire numeric range of a binary-width cap still has that bit width.
This supplies primitive width contracts without requiring a polynomial arity. -/
theorem binary_width (header bits n : Nat)
    (encoded : ∀ n, Q.size data.nat n ≤ Nat.size n + header)
    (hn : n ≤ 2 ^ bits - 1) : Q.size data.nat n ≤ bits + header := by
  have hp : 0 < 2 ^ bits := Nat.two_pow_pos bits
  have hs : Nat.size n ≤ bits := Nat.size_le.mpr (by omega)
  exact (encoded n).trans (Nat.add_le_add_right hs header)

end NatValueLaws

end Signatures.Runtime.BackendProgram
