import Signatures.Runtime.WeightedExtraction
import Signatures.Runtime.WeightedCoefficientsDescription
import Signatures.Runtime.BackendWeightedEvaluateDescription

/-! Stored syntax of complete weighted extraction. The two generated-message
term routines are counted separately, along with chronological coefficient
matching, evaluator loops, actual reads, defaults and final arithmetic. -/

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate LazyAGM.ReplySyntax

variable {indexTy messageTy value : Ty CryptoAtom}
  (allowance : Nat) (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
  (readerSize : Nat)

theorem evaluateRows_description
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    Language.descriptionBound allowance primitiveSize (fun _ => readerSize) (evaluateRows zero combine) ≤
      readerSize + Expression.descriptionBound allowance primitiveSize zero +
      Expression.descriptionBound allowance primitiveSize combine +
      primitiveSize .natEq + primitiveSize .natSub + 2 * primitiveSize .natAdd +
      736 * allowance + 92 := by
  simp only [evaluateRows, evalBody, selectRow, evalUpdate, listLength,
    Language.descriptionBound, Expression.descriptionBound, Expression.descriptionBound_weakenTail,
    index, indexBody, v0, v1, v2, v3, Expression.variableDescription]
  omega

theorem good_description
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy)) :
    Language.descriptionBound allowance primitiveSize (fun _ => readerSize) (good terms default) ≤
      3 * readerSize + 2 * Expression.descriptionBound allowance primitiveSize terms +
      Expression.descriptionBound allowance primitiveSize default + primitiveSize .one +
      5 * primitiveSize .zero + 4 * primitiveSize .add + 5 * primitiveSize .mul +
      5 * primitiveSize .natEq + 5 * primitiveSize .natSub + 8 * primitiveSize .natAdd +
      primitiveSize .sub + primitiveSize .div + 8192 * allowance + 512 := by
  have he := evaluateRows_description allowance primitiveSize readerSize
    (indexTy := indexTy) (.op .zero .unit) goodCombine
  have hh := Coefficients.signedTerms_description allowance primitiveSize (hashTerms (indexTy := indexTy))
  have hs := Coefficients.signedTerms_description allowance primitiveSize terms
  simp only [good, evaluateCoefficients, evaluateTarget, defaultRow, goodCombine, hashTerms,
    Language.descriptionBound, Expression.descriptionBound, Expression.descriptionBound_weakenTail,
    Expression.argumentsDescription, v0, v1, v2, v3, v4, Expression.variableDescription,
    Coefficients.description] at *
  omega

theorem bad_description
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy)) :
    Language.descriptionBound allowance primitiveSize (fun _ => readerSize) (bad terms default) ≤
      2 * readerSize + 2 * Expression.descriptionBound allowance primitiveSize terms +
      Expression.descriptionBound allowance primitiveSize default +
      5 * primitiveSize .zero + 4 * primitiveSize .add + 5 * primitiveSize .mul +
      3 * primitiveSize .natEq + 3 * primitiveSize .natSub + 5 * primitiveSize .natAdd +
      2 * primitiveSize .sub + primitiveSize .neg + primitiveSize .div + 8192 * allowance + 512 := by
  have he := evaluateRows_description allowance primitiveSize readerSize
    (indexTy := indexTy) (.pair (.op .zero .unit) (.op .zero .unit)) badCombine
  have hs := Coefficients.signedTerms_description allowance primitiveSize terms
  simp only [bad, evaluateCoefficients, evaluateTarget, defaultRow, badCombine,
    Language.descriptionBound, Expression.descriptionBound, Expression.descriptionBound_weakenTail,
    Expression.argumentsDescription, v0, v1, v2, v3, Expression.variableDescription,
    Coefficients.description] at *
  omega

end Signatures.Runtime.WeightedAGM.Extract
