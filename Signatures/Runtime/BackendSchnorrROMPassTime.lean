import Signatures.Runtime.BackendSchnorrROMPassPolynomial

/-! Numerical inputs to the complete pass runtime. Separating these numbers
from the typed implementation lets the polynomial theorem apply when the curve,
message types and representations vary with the security parameter. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape

/-- Original sampler, primitive, port and routing resources; no completed pass
or component runtime is supplied. Numeric arities and counters are absent. -/
structure TimeInputs where
  work : Nat
  visits : Nat
  queries : Nat
  sourceWidth : Nat
  savedCap : Nat
  tickTime : Nat
  comparisonTime : Nat
  zeroTime : Nat
  addTime : Nat
  requestTime : Nat
  responseTime : Nat
  queryTime : Nat
  arityTime : Nat
  replyTime : Nat
  messageTime : Nat
  pointTime : Nat
  scaleTime : Nat
  subTime : Nat
  portWidth : Nat
  encodeTime : Nat
  tagTime : Nat
  routeWidth : Nat
  callerTickTime : Nat
  inputTime : Nat
  outputTime : Nat
  optionalTime : Nat

def TimeInputs.time (inputs : TimeInputs) (overhead : Nat → Nat) (bound : ExecutionCost)
    (width tapeWidth managedCap liveCap remainingCap fuel : Nat) : Nat :=
  timeBudget overhead (frameWidth width managedCap liveCap inputs.routeWidth)
    (NativeHandler.callerTime overhead inputs.routeWidth fuel (bound.work + 2 * bound.queries + 2) (fun _ => bound.queries)
      (NativeHandler.timeBudget overhead inputs.work inputs.visits inputs.queries inputs.sourceWidth tapeWidth
        inputs.savedCap remainingCap inputs.tickTime inputs.comparisonTime inputs.zeroTime inputs.addTime
        inputs.requestTime inputs.responseTime inputs.queryTime inputs.arityTime inputs.replyTime
        width managedCap liveCap inputs.messageTime inputs.pointTime inputs.scaleTime inputs.subTime
        inputs.portWidth inputs.encodeTime inputs.tagTime) inputs.callerTickTime)
    (finalHashTime overhead inputs.work inputs.visits inputs.queries tapeWidth inputs.savedCap remainingCap
      inputs.tickTime inputs.comparisonTime inputs.zeroTime inputs.queryTime width liveCap
      inputs.messageTime inputs.pointTime) inputs.inputTime inputs.outputTime inputs.optionalTime

/-- Only original numerical fields need polynomial bounds. -/
structure TimeInputs.Polynomial (inputs : Nat → TimeInputs) : Prop where
  work : PolynomiallyBounded (fun n => (inputs n).work)
  visits : PolynomiallyBounded (fun n => (inputs n).visits)
  queries : PolynomiallyBounded (fun n => (inputs n).queries)
  sourceWidth : PolynomiallyBounded (fun n => (inputs n).sourceWidth)
  savedCap : PolynomiallyBounded (fun n => (inputs n).savedCap)
  tickTime : PolynomiallyBounded (fun n => (inputs n).tickTime)
  comparisonTime : PolynomiallyBounded (fun n => (inputs n).comparisonTime)
  zeroTime : PolynomiallyBounded (fun n => (inputs n).zeroTime)
  addTime : PolynomiallyBounded (fun n => (inputs n).addTime)
  requestTime : PolynomiallyBounded (fun n => (inputs n).requestTime)
  responseTime : PolynomiallyBounded (fun n => (inputs n).responseTime)
  queryTime : PolynomiallyBounded (fun n => (inputs n).queryTime)
  arityTime : PolynomiallyBounded (fun n => (inputs n).arityTime)
  replyTime : PolynomiallyBounded (fun n => (inputs n).replyTime)
  messageTime : PolynomiallyBounded (fun n => (inputs n).messageTime)
  pointTime : PolynomiallyBounded (fun n => (inputs n).pointTime)
  scaleTime : PolynomiallyBounded (fun n => (inputs n).scaleTime)
  subTime : PolynomiallyBounded (fun n => (inputs n).subTime)
  portWidth : PolynomiallyBounded (fun n => (inputs n).portWidth)
  encodeTime : PolynomiallyBounded (fun n => (inputs n).encodeTime)
  tagTime : PolynomiallyBounded (fun n => (inputs n).tagTime)
  routeWidth : PolynomiallyBounded (fun n => (inputs n).routeWidth)
  callerTickTime : PolynomiallyBounded (fun n => (inputs n).callerTickTime)
  inputTime : PolynomiallyBounded (fun n => (inputs n).inputTime)
  outputTime : PolynomiallyBounded (fun n => (inputs n).outputTime)
  optionalTime : PolynomiallyBounded (fun n => (inputs n).optionalTime)

theorem TimeInputs.time_polynomial (inputs : Nat → TimeInputs) (overhead : Nat → Nat → Nat)
    (bound : Nat → ExecutionCost) (width tapeWidth managedCap liveCap remainingCap fuel : Nat → Nat)
    (hInputs : TimeInputs.Polynomial inputs) (hOverhead : PolynomialOverhead overhead)
    (hCallerWork : PolynomiallyBounded (fun n => (bound n).work))
    (hCallerQueries : PolynomiallyBounded (fun n => (bound n).queries))
    (hWidth : PolynomiallyBounded width) (hTape : PolynomiallyBounded tapeWidth)
    (hManaged : PolynomiallyBounded managedCap) (hLive : PolynomiallyBounded liveCap)
    (hRemaining : PolynomiallyBounded remainingCap) (hFuel : PolynomiallyBounded fuel) :
    PolynomiallyBounded (fun n => (inputs n).time (overhead n) (bound n)
      (width n) (tapeWidth n) (managedCap n) (liveCap n) (remainingCap n) (fuel n)) := by
  exact resourcesTime_polynomial overhead
    (fun n => (inputs n).work) (fun n => (inputs n).visits) (fun n => (inputs n).queries) (fun n => (inputs n).sourceWidth)
    tapeWidth (fun n => (inputs n).savedCap) remainingCap (fun n => (inputs n).tickTime)
    (fun n => (inputs n).comparisonTime) (fun n => (inputs n).zeroTime) (fun n => (inputs n).addTime) (fun n => (inputs n).requestTime)
    (fun n => (inputs n).responseTime) (fun n => (inputs n).queryTime) (fun n => (inputs n).arityTime) (fun n => (inputs n).replyTime)
    width managedCap liveCap (fun n => (inputs n).messageTime)
    (fun n => (inputs n).pointTime) (fun n => (inputs n).scaleTime) (fun n => (inputs n).subTime) (fun n => (inputs n).portWidth)
    (fun n => (inputs n).encodeTime) (fun n => (inputs n).tagTime)
    bound (fun n => (inputs n).routeWidth) fuel (fun n => (inputs n).callerTickTime)
    (fun n => (inputs n).inputTime) (fun n => (inputs n).outputTime) (fun n => (inputs n).optionalTime)
    hCallerWork hCallerQueries hInputs.routeWidth hFuel hInputs.callerTickTime
    hInputs.inputTime hInputs.outputTime hInputs.optionalTime hOverhead
    hInputs.work hInputs.visits hInputs.queries hInputs.sourceWidth hTape hInputs.savedCap
    hRemaining hInputs.tickTime hInputs.comparisonTime hInputs.zeroTime hInputs.addTime
    hInputs.requestTime hInputs.responseTime hInputs.queryTime hInputs.arityTime hInputs.replyTime
    hWidth hManaged hLive hInputs.messageTime hInputs.pointTime hInputs.scaleTime hInputs.subTime
    hInputs.portWidth hInputs.encodeTime hInputs.tagTime

end Signatures.Runtime.Schnorr.ListROM.NativePass
