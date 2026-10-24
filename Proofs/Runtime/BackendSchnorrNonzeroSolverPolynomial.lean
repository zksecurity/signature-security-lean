import Proofs.Runtime.BackendSchnorrNonzeroSolverBudget
import Proofs.Runtime.BackendSchnorrNonzeroForkPolynomial
import Proofs.Runtime.BackendSchnorrROMSolverPolynomial

/-! Complete nonzero-nonce solver time is polynomial from original resources.
Both passes, selection/reset, guarded extraction and fallback are included. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver

open BackendProgram RawTape ListROM

theorem resourcesTime_polynomial (overhead : Nat → Nat → Nat) (bound : Nat → ExecutionCost)
    (width tapeWidth managedCap liveCap fuel : Nat → Nat) (first second : Nat → NativePass.TimeInputs)
    (scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime
      extractionScalarTime fieldSubTime divTime : Nat → Nat)
    (hFirst : NativePass.TimeInputs.Polynomial first) (hSecond : NativePass.TimeInputs.Polynomial second)
    (hOverhead : PolynomialOverhead overhead)
    (hCallerWork : PolynomiallyBounded (fun n => (bound n).work))
    (hCallerQueries : PolynomiallyBounded (fun n => (bound n).queries))
    (hWidth : PolynomiallyBounded width) (hTape : PolynomiallyBounded tapeWidth)
    (hManaged : PolynomiallyBounded managedCap) (hLive : PolynomiallyBounded liveCap)
    (hFuel : PolynomiallyBounded fuel)
    (hScale : PolynomiallyBounded scaleTime) (hAdd : PolynomiallyBounded addTime)
    (hMessage : PolynomiallyBounded messageTime) (hPoint : PolynomiallyBounded pointTime)
    (hIncrement : PolynomiallyBounded incrementTime) (hComparison : PolynomiallyBounded comparisonTime)
    (hScalarComparison : PolynomiallyBounded scalarComparisonTime) (hSubtract : PolynomiallyBounded subtractTime)
    (hExtractionScalar : PolynomiallyBounded extractionScalarTime)
    (hFieldSub : PolynomiallyBounded fieldSubTime) (hDiv : PolynomiallyBounded divTime) :
    PolynomiallyBounded (fun n => resourcesTime (overhead n) (bound n)
      (width n) (tapeWidth n) (managedCap n) (liveCap n) (fuel n) (first n) (second n)
      (scaleTime n) (addTime n) (messageTime n) (pointTime n) (incrementTime n)
      (comparisonTime n) (scalarComparisonTime n) (subtractTime n)
      (extractionScalarTime n) (fieldSubTime n) (divTime n)) := by
  have hfork := NativeROMFork.resourcesTime_polynomial overhead bound width tapeWidth managedCap liveCap fuel first second
    scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime
    hFirst hSecond hOverhead hCallerWork hCallerQueries hWidth hTape hManaged hLive hFuel
    hScale hAdd hMessage hPoint hIncrement hComparison hScalarComparison hSubtract
  have hsample := ExecutionProfile.runtimeBound_polynomial overhead tapeWidth
    (fun n => (first n).fieldWork) (fun n => (first n).fieldVisits) (fun n => (first n).fieldQueries)
    (fun n => (first n).tickTime) (fun n => (first n).queryTime)
    hOverhead hTape hFirst.fieldWork hFirst.fieldVisits hFirst.fieldQueries hFirst.tickTime hFirst.queryTime
  have hLiveNext := hLive.add (PolynomiallyBounded.const 1)
  have hextract := NativeExtraction.runtimeBound_polynomial overhead width managedCap (fun n => liveCap n + 1)
    pointTime extractionScalarTime fieldSubTime divTime (fun n => (first n).zeroTime) _
    hOverhead hWidth hManaged hLiveNext hPoint hExtractionScalar hFieldSub hDiv hFirst.zeroTime hsample
  have hframe := NativeExtraction.frameWidth_polynomial width managedCap (fun n => liveCap n + 1) hWidth hManaged hLiveNext
  exact (hfork.add hextract).add ((PolynomiallyBounded.const 128).mul
    (hOverhead.apply ((PolynomiallyBounded.const 8192).mul hframe)))


end Signatures.Runtime.Schnorr.NonzeroListROM.NativeSolver
