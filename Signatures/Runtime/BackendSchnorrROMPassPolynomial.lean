import Signatures.Runtime.BackendSchnorrROMPassBudget
import Signatures.Runtime.BackendSchnorrROMCallerPolynomial

/-! Polynomial closure of the complete pass bound. The caller and final hash
budgets are derived from the same original resources as the runtime theorem;
neither numeric sampling arities nor message-domain cardinalities occur. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativePass

open BackendProgram RawTape

theorem frameWidth_polynomial (width managedCap liveCap routeWidth : Nat → Nat)
    (hWidth : PolynomiallyBounded width) (hManaged : PolynomiallyBounded managedCap)
    (hLive : PolynomiallyBounded liveCap) (hRoute : PolynomiallyBounded routeWidth) :
    PolynomiallyBounded (fun n => frameWidth (width n) (managedCap n) (liveCap n) (routeWidth n)) := by
  unfold frameWidth NativeComponents.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

theorem finalHashTime_polynomial (overhead : Nat → Nat → Nat)
    (work visits queries tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime queryTime
      width liveCap messageTime pointTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead)
    (hWork : PolynomiallyBounded work) (hVisits : PolynomiallyBounded visits)
    (hQueries : PolynomiallyBounded queries) (hTape : PolynomiallyBounded tapeWidth)
    (hSaved : PolynomiallyBounded savedCap) (hRemaining : PolynomiallyBounded remainingCap)
    (hTick : PolynomiallyBounded tickTime) (hCompare : PolynomiallyBounded comparisonTime)
    (hZero : PolynomiallyBounded zeroTime) (hQuery : PolynomiallyBounded queryTime)
    (hWidth : PolynomiallyBounded width) (hLive : PolynomiallyBounded liveCap)
    (hMessage : PolynomiallyBounded messageTime) (hPoint : PolynomiallyBounded pointTime) :
    PolynomiallyBounded (fun n => finalHashTime (overhead n) (work n) (visits n) (queries n)
      (tapeWidth n) (savedCap n) (remainingCap n) (tickTime n) (comparisonTime n) (zeroTime n)
      (queryTime n) (width n) (liveCap n) (messageTime n) (pointTime n)) := by
  have hsample := ExecutionProfile.runtimeBound_polynomial overhead tapeWidth work visits queries tickTime queryTime
    hOverhead hTape hWork hVisits hQueries hTick hQuery
  have hdraw := NativeDraw.challengeTime_polynomial overhead tapeWidth savedCap remainingCap comparisonTime zeroTime _
    hOverhead hTape hSaved hRemaining hCompare hZero hsample
  exact (NativeCache.liveTime_polynomial overhead _ liveCap messageTime pointTime _ hOverhead
    ((PolynomiallyBounded.const 3).mul hWidth) hLive hMessage hPoint hdraw).add hZero

theorem timeBudget_polynomial (overhead : Nat → Nat → Nat)
    (frame callerTime hashTime inputTime outputTime optionalTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hFrame : PolynomiallyBounded frame)
    (hCaller : PolynomiallyBounded callerTime) (hHash : PolynomiallyBounded hashTime)
    (hInput : PolynomiallyBounded inputTime) (hOutput : PolynomiallyBounded outputTime)
    (hOptional : PolynomiallyBounded optionalTime) :
    PolynomiallyBounded (fun n => timeBudget (overhead n) (frame n) (callerTime n) (hashTime n)
      (inputTime n) (outputTime n) (optionalTime n)) := by
  unfold timeBudget
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

theorem resourcesTime_polynomial (overhead : Nat → Nat → Nat)
    (work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime
      scaleTime subTime portWidth encodeTime tagTime : Nat → Nat)
    (bound : Nat → ExecutionCost) (routeWidth fuel callerTickTime inputTime outputTime optionalTime : Nat → Nat)
    (hCallerWork : PolynomiallyBounded (fun n => (bound n).work))
    (hCallerQueries : PolynomiallyBounded (fun n => (bound n).queries))
    (hRoute : PolynomiallyBounded routeWidth) (hFuel : PolynomiallyBounded fuel)
    (hCallerTick : PolynomiallyBounded callerTickTime)
    (hInput : PolynomiallyBounded inputTime) (hOutput : PolynomiallyBounded outputTime)
    (hOptional : PolynomiallyBounded optionalTime)
    (hOverhead : PolynomialOverhead overhead)
    (hWork : PolynomiallyBounded work) (hVisits : PolynomiallyBounded visits)
    (hQueries : PolynomiallyBounded queries) (hSourceWidth : PolynomiallyBounded sourceWidth)
    (hTapeWidth : PolynomiallyBounded tapeWidth) (hSaved : PolynomiallyBounded savedCap)
    (hRemaining : PolynomiallyBounded remainingCap) (hTick : PolynomiallyBounded tickTime)
    (hCompare : PolynomiallyBounded comparisonTime) (hZero : PolynomiallyBounded zeroTime)
    (hAdd : PolynomiallyBounded addTime) (hRequest : PolynomiallyBounded requestTime)
    (hResponse : PolynomiallyBounded responseTime) (hQuery : PolynomiallyBounded queryTime)
    (hArity : PolynomiallyBounded arityTime) (hReply : PolynomiallyBounded replyTime)
    (hWidth : PolynomiallyBounded width) (hManaged : PolynomiallyBounded managedCap)
    (hLive : PolynomiallyBounded liveCap) (hMessage : PolynomiallyBounded messageTime)
    (hPoint : PolynomiallyBounded pointTime) (hScale : PolynomiallyBounded scaleTime)
    (hSub : PolynomiallyBounded subTime) (hPort : PolynomiallyBounded portWidth)
    (hEncode : PolynomiallyBounded encodeTime) (hTag : PolynomiallyBounded tagTime) :
    PolynomiallyBounded (fun n => timeBudget (overhead n)
      (frameWidth (width n) (managedCap n) (liveCap n) (routeWidth n))
      (NativeHandler.callerTime (overhead n) (routeWidth n) (fuel n)
        ((bound n).work + 2 * (bound n).queries + 2) (fun _ => (bound n).queries)
        (NativeHandler.timeBudget (overhead n) (work n) (visits n) (queries n) (sourceWidth n)
          (tapeWidth n) (savedCap n) (remainingCap n) (tickTime n) (comparisonTime n) (zeroTime n)
          (addTime n) (requestTime n) (responseTime n) (queryTime n) (arityTime n) (replyTime n)
          (width n) (managedCap n) (liveCap n) (messageTime n) (pointTime n) (scaleTime n) (subTime n)
          (portWidth n) (encodeTime n) (tagTime n)) (callerTickTime n))
      (finalHashTime (overhead n) (work n) (visits n) (queries n) (tapeWidth n) (savedCap n)
        (remainingCap n) (tickTime n) (comparisonTime n) (zeroTime n) (queryTime n) (width n)
        (liveCap n) (messageTime n) (pointTime n)) (inputTime n) (outputTime n) (optionalTime n)) := by
  have hcaller := NativeHandler.callerResourcesTime_polynomial overhead work visits queries sourceWidth tapeWidth
    savedCap remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime
    replyTime width managedCap liveCap messageTime pointTime scaleTime subTime portWidth encodeTime tagTime
    bound routeWidth fuel callerTickTime hCallerWork hCallerQueries hRoute hFuel hCallerTick hOverhead
    hWork hVisits hQueries hSourceWidth hTapeWidth hSaved hRemaining hTick hCompare hZero hAdd hRequest hResponse
    hQuery hArity hReply hWidth hManaged hLive hMessage hPoint hScale hSub hPort hEncode hTag
  have hfinal := finalHashTime_polynomial overhead work visits queries tapeWidth savedCap remainingCap tickTime
    comparisonTime zeroTime queryTime width liveCap messageTime pointTime hOverhead hWork hVisits hQueries
    hTapeWidth hSaved hRemaining hTick hCompare hZero hQuery hWidth hLive hMessage hPoint
  exact timeBudget_polynomial overhead _ _ _ inputTime outputTime optionalTime hOverhead
    (frameWidth_polynomial width managedCap liveCap routeWidth hWidth hManaged hLive hRoute)
    hcaller hfinal hInput hOutput hOptional

end Signatures.Runtime.Schnorr.ListROM.NativePass
