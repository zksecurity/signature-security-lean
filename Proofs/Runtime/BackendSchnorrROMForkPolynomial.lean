import Proofs.Runtime.BackendSchnorrROMForkBudget
import Proofs.Runtime.BackendSchnorrROMSelectionPolynomial

/-! Polynomial closure of the complete installed fork runtime, from original
caller/sampler resources and primitive costs. Neither completed pass efficiency
nor a polynomial numeric-arity or counter bound is assumed. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeROMFork

open BackendProgram RawTape

theorem controllerWidth_polynomial (width managedCap liveCap : Nat → Nat)
    (hWidth : PolynomiallyBounded width) (hManaged : PolynomiallyBounded managedCap)
    (hLive : PolynomiallyBounded liveCap) :
    PolynomiallyBounded (fun n => controllerWidth (width n) (managedCap n) (liveCap n)) := by
  unfold controllerWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

theorem resourcesTime_polynomial (overhead : Nat → Nat → Nat) (bound : Nat → ExecutionCost)
    (width tapeWidth managedCap liveCap fuel : Nat → Nat) (first second : Nat → NativePass.TimeInputs)
    (scaleTime addTime messageTime pointTime incrementTime comparisonTime scalarComparisonTime subtractTime : Nat → Nat)
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
    (hScalarComparison : PolynomiallyBounded scalarComparisonTime) (hSubtract : PolynomiallyBounded subtractTime) :
    PolynomiallyBounded (fun n => resourcesTime (overhead n) (bound n)
      (width n) (tapeWidth n) (managedCap n) (liveCap n) (fuel n) (first n) (second n)
      (scaleTime n) (addTime n) (messageTime n) (pointTime n) (incrementTime n)
      (comparisonTime n) (scalarComparisonTime n) (subtractTime n)) := by
  have hFirstTime := NativePass.TimeInputs.time_polynomial first overhead bound width tapeWidth managedCap liveCap
    (fun _ => 0) fuel hFirst hOverhead hCallerWork hCallerQueries hWidth hTape hManaged hLive
    (PolynomiallyBounded.const 0) hFuel
  have hSecondTime := NativePass.TimeInputs.time_polynomial second overhead bound width tapeWidth managedCap liveCap
    (fun n => (first n).savedCap + 2) fuel hSecond hOverhead hCallerWork hCallerQueries hWidth hTape hManaged hLive
    (hFirst.savedCap.add (PolynomiallyBounded.const 2)) hFuel
  have hLiveNext := hLive.add (PolynomiallyBounded.const 1)
  have hSelection := NativeSelection.timeBudget_polynomial overhead width managedCap (fun n => liveCap n + 1)
    scaleTime addTime messageTime pointTime incrementTime comparisonTime
    hOverhead hWidth hManaged hLiveNext hScale hAdd hMessage hPoint hIncrement hComparison
  have hSample := ExecutionProfile.runtimeBound_polynomial overhead tapeWidth
    (fun n => (first n).work) (fun n => (first n).visits) (fun n => (first n).queries)
    (fun n => (first n).tickTime) (fun n => (first n).queryTime)
    hOverhead hTape hFirst.work hFirst.visits hFirst.queries hFirst.tickTime hFirst.queryTime
  exact NativeFork.runtimeBoundWithTapeWidth_polynomial overhead _ tapeWidth
    (fun n => (first n).savedCap + 1) (fun n => (second n).savedCap + 1) _ _ _ _
    (fun n => (first n).comparisonTime) scalarComparisonTime subtractTime (fun n => (first n).zeroTime)
    hOverhead (controllerWidth_polynomial width managedCap _ hWidth hManaged hLiveNext) hTape
    (hFirst.savedCap.add (PolynomiallyBounded.const 1)) (hSecond.savedCap.add (PolynomiallyBounded.const 1))
    hFirstTime hSecondTime hSelection hSample hFirst.comparisonTime hScalarComparison hSubtract hFirst.zeroTime

end Signatures.Runtime.Schnorr.ListROM.NativeROMFork
