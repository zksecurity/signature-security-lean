import Proofs.Runtime.WeightedTerms
import Proofs.Runtime.BackendExpressionSize

/-! Stored-code bounds for term generation. Primitive descriptions are charged
separately; degree/dimension and unary literals are part of the stored program.
These bounds are polynomial in the numerical degree/dimension. -/

namespace Signatures.Runtime.WeightedAGM.Terms

open BackendProgram.Expression

variable (allowance : Nat) (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)

def oopsFromDescription (d n start : Nat) : Nat :=
  n * (start + n + primitiveSize (.finOfNat d) + primitiveSize .mul + 32 * allowance) +
    3 * allowance

theorem oopsFrom_description (d n start : Nat) {Γ : List (Ty CryptoAtom)} :
    descriptionBound allowance primitiveSize (oopsFrom d n start (Γ := Γ)) ≤
      oopsFromDescription allowance primitiveSize d n start := by
  induction n generalizing start Γ with
  | zero => simp [oopsFrom, descriptionBound, oopsFromDescription]
  | succ n ih =>
      have h := ih (start + 1) (Γ := [scalar, Weights.oopsMessage] ++ Γ)
      simp only [oopsFrom, descriptionBound, variableDescription]
      dsimp only [oopsFromDescription] at h ⊢
      nlinarith

def oopsDescription (d : Nat) : Nat :=
  oopsFromDescription allowance primitiveSize d (d + 1) 0 + primitiveSize .one + 5 * allowance

theorem oops_description (d : Nat) :
    descriptionBound allowance primitiveSize (oops d) ≤ oopsDescription allowance primitiveSize d := by
  have h := oopsFrom_description allowance primitiveSize d (d + 1) 0 (Γ := [])
  simp only [oops, descriptionBound, oopsDescription]
  omega

def proximityFromDescription (ell n start : Nat) : Nat :=
  n * (start + n + primitiveSize (.finOfNat ell) + 29 * allowance) + 3 * allowance

theorem proximityFrom_description (ell n start : Nat) {Γ : List (Ty CryptoAtom)} :
    descriptionBound allowance primitiveSize (proximityFrom ell n start (Γ := Γ)) ≤
      proximityFromDescription allowance primitiveSize ell n start := by
  induction n generalizing start Γ with
  | zero => simp [proximityFrom, descriptionBound, proximityFromDescription]
  | succ n ih =>
      have h := ih (start + 1) (Γ := [Weights.proximityTupleMessage (n + 1)] ++ Γ)
      simp only [proximityFrom, descriptionBound, variableDescription]
      dsimp only [proximityFromDescription] at h ⊢
      nlinarith

def proximityDescription (ell : Nat) : Nat :=
  proximityFromDescription allowance primitiveSize ell ell 1 +
    primitiveSize (.finZero ell) + primitiveSize .one + 12 * allowance

theorem proximity_description (ell : Nat) :
    descriptionBound allowance primitiveSize (proximity ell) ≤
      proximityDescription allowance primitiveSize ell := by
  have h := proximityFrom_description allowance primitiveSize ell ell 1 (Γ := [])
  simp only [proximity, descriptionBound, variableDescription, proximityDescription]
  omega

end Signatures.Runtime.WeightedAGM.Terms
