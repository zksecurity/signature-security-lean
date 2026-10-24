import Proofs.Runtime.WeightedCoefficients
import Proofs.Runtime.WeightedTermsDescription
import Proofs.Runtime.BackendTokenRows

/-! Stored-code accounting for signing-coefficient expansion. The generated
term routine is stored once in the fold body, independently of the number of
signing replies. Chronological matching, multiplication, both folds and the
final reversal are charged. These are code bounds, not runtime claims. -/

namespace Signatures.Runtime.WeightedAGM.Coefficients

open Terms BackendProgram.Expression

variable {indexTy messageTy : Ty CryptoAtom}
  (allowance : Nat) (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)

def description (termDescription : Nat) : Nat :=
  termDescription + primitiveSize .mul + primitiveSize .zero + primitiveSize .natEq +
    primitiveSize .natSub + primitiveSize .natAdd + 2400 * allowance + 16

theorem signedTerms_description (terms : Expr CryptoOp [messageTy] (.list (termTy indexTy))) :
    descriptionBound allowance primitiveSize (signedTerms terms) ≤
      description allowance primitiveSize (descriptionBound allowance primitiveSize terms) := by
  simp only [signedTerms, expandRows, expandStep, scalePrepend, AGM.tokenRows,
    AGM.attachTable, AGM.attachFold, AGM.attachBody, index, indexBody, reverseList,
    descriptionBound, descriptionBound_weakenTail, variableDescription]
  dsimp only [description]
  omega

theorem oops_description (d : Nat) :
    descriptionBound allowance primitiveSize (signedTerms (Terms.oops d)) ≤
      description allowance primitiveSize (oopsDescription allowance primitiveSize d) := by
  have ht := Terms.oops_description allowance primitiveSize d
  have hs := signedTerms_description allowance primitiveSize (Terms.oops d)
  dsimp only [description] at *
  omega

theorem proximity_description (ell : Nat) :
    descriptionBound allowance primitiveSize (signedTerms (Terms.proximity ell)) ≤
      description allowance primitiveSize (proximityDescription allowance primitiveSize ell) := by
  have ht := Terms.proximity_description allowance primitiveSize ell
  have hs := signedTerms_description allowance primitiveSize (Terms.proximity ell)
  dsimp only [description] at *
  omega

end Signatures.Runtime.WeightedAGM.Coefficients
