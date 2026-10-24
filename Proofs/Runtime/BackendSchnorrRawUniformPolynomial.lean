import Proofs.Runtime.BackendSchnorrRawUniformBudget
import Proofs.Runtime.PolynomialResources

/-! Polynomial closure of the proved native private-draw runtime formula.
One fixed polynomial bounds each component across security parameters. Numeric
sampling arities need not be polynomial; encoded widths and actual tape lengths do. -/

namespace Signatures.Runtime.Schnorr.RawTape.NativeUniform

private theorem max_polynomial {f g : Nat → Nat}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩)

theorem runtimeBound_polynomial (overhead : Nat → Nat → Nat)
    (width savedCap remainingCap comparisonTime zeroTime addTime requestTime responseTime queryTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead)
    (hWidth : PolynomiallyBounded width) (hSaved : PolynomiallyBounded savedCap)
    (hRemaining : PolynomiallyBounded remainingCap)
    (hCompare : PolynomiallyBounded comparisonTime) (hZero : PolynomiallyBounded zeroTime)
    (hAdd : PolynomiallyBounded addTime) (hRequest : PolynomiallyBounded requestTime)
    (hResponse : PolynomiallyBounded responseTime) (hQuery : PolynomiallyBounded queryTime) :
    PolynomiallyBounded (fun n => runtimeBound (overhead n) (width n) (savedCap n) (remainingCap n)
      (comparisonTime n) (zeroTime n) (addTime n) (requestTime n) (responseTime n) (queryTime n)) := by
  unfold runtimeBound prepareTime saveTime saveFrameWidth SeedTape.NativeScan.scanTime
    SeedTape.NativeScan.forwardTime SeedTape.NativeScan.frameWidth ListSnoc.snocTime ListSnoc.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply max_polynomial
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.RawTape.NativeUniform
