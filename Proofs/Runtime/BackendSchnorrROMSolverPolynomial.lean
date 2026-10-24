import Proofs.Runtime.BackendSchnorrROMSolverBudget
import Proofs.Runtime.BackendSchnorrROMForkPolynomial

/-! Polynomial runtime of the complete native general Schnorr ROM solver.
Both pass executions, the fork, extraction and fallback are derived from original
component resource families; no completed solver efficiency is assumed. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM

open BackendProgram RawTape

namespace NativeExtraction

theorem frameWidth_polynomial (width managedCap liveCap : Nat → Nat)
    (hWidth : PolynomiallyBounded width) (hManaged : PolynomiallyBounded managedCap)
    (hLive : PolynomiallyBounded liveCap) :
    PolynomiallyBounded (fun n => frameWidth (width n) (managedCap n) (liveCap n)) := by
  unfold frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

theorem runtimeBound_polynomial (overhead : Nat → Nat → Nat)
    (width managedCap liveCap pointTime scalarTime subTime divTime zeroTime sampleTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hManaged : PolynomiallyBounded managedCap) (hLive : PolynomiallyBounded liveCap)
    (hPoint : PolynomiallyBounded pointTime) (hScalar : PolynomiallyBounded scalarTime)
    (hSub : PolynomiallyBounded subTime) (hDiv : PolynomiallyBounded divTime)
    (hZero : PolynomiallyBounded zeroTime) (hSample : PolynomiallyBounded sampleTime) :
    PolynomiallyBounded (fun n => runtimeBound (overhead n) (width n) (managedCap n) (liveCap n)
      (pointTime n) (scalarTime n) (subTime n) (divTime n) (zeroTime n) (sampleTime n)) := by
  unfold runtimeBound localTime frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

end NativeExtraction

namespace NativeSolver

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
    (fun n => (first n).work) (fun n => (first n).visits) (fun n => (first n).queries)
    (fun n => (first n).tickTime) (fun n => (first n).queryTime)
    hOverhead hTape hFirst.work hFirst.visits hFirst.queries hFirst.tickTime hFirst.queryTime
  have hLiveNext := hLive.add (PolynomiallyBounded.const 1)
  have hextract := NativeExtraction.runtimeBound_polynomial overhead width managedCap (fun n => liveCap n + 1)
    pointTime extractionScalarTime fieldSubTime divTime (fun n => (first n).zeroTime) _
    hOverhead hWidth hManaged hLiveNext hPoint hExtractionScalar hFieldSub hDiv hFirst.zeroTime hsample
  have hframe := NativeExtraction.frameWidth_polynomial width managedCap (fun n => liveCap n + 1) hWidth hManaged hLiveNext
  exact (hfork.add hextract).add ((PolynomiallyBounded.const 128).mul
    (hOverhead.apply ((PolynomiallyBounded.const 8192).mul hframe)))

end NativeSolver

end Signatures.Runtime.Schnorr.ListROM
