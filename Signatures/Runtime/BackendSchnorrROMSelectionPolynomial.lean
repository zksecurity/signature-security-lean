import Signatures.Runtime.BackendSchnorrROMLiveIndexBudget
import Signatures.Runtime.BackendSchnorrROMSelectionDescription
import Signatures.Runtime.BackendSchnorrROMPassPolynomial

/-! Polynomial closure for the proved native lookup and selector-description
bounds. Complete selector runtime composition remains a separate obligation. -/

namespace Signatures.Runtime.Schnorr.ListROM.NativeSelection

open BackendProgram

theorem indexTime_polynomial (overhead : Nat → Nat → Nat)
    (width cap messageTime pointTime incrementTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap) (hMessage : PolynomiallyBounded messageTime)
    (hPoint : PolynomiallyBounded pointTime) (hIncrement : PolynomiallyBounded incrementTime) :
    PolynomiallyBounded (fun n => indexTime (overhead n) (width n) (cap n)
      (messageTime n) (pointTime n) (incrementTime n)) := by
  unfold indexTime indexWidth indexFoldTime indexFoldWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

theorem description_polynomial (scaleSize addSize pointSize messageSize incrementSize comparisonSize
    qH allowance : Nat → Nat)
    (hScale : PolynomiallyBounded scaleSize) (hAdd : PolynomiallyBounded addSize)
    (hPoint : PolynomiallyBounded pointSize) (hMessage : PolynomiallyBounded messageSize)
    (hIncrement : PolynomiallyBounded incrementSize) (hComparison : PolynomiallyBounded comparisonSize)
    (hQueries : PolynomiallyBounded qH) (hAllowance : PolynomiallyBounded allowance) :
    PolynomiallyBounded (fun n => 2 * scaleSize n + addSize n + 2 * pointSize n + messageSize n +
      incrementSize n + comparisonSize n + qH n + 4096 * allowance n + 16) := by
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.ListROM.NativeSelection
