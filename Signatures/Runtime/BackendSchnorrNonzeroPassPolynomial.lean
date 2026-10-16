import Signatures.Runtime.BackendSchnorrNonzeroPassBudget
import Signatures.Runtime.BackendSchnorrROMPassPolynomial

/-! Polynomial closure of complete nonzero-nonce pass runtime from original
caller and sampler resources and the local encoding/operation contracts. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativePass

open ListROM.NativePass

theorem resourcesTime_polynomial (overhead : Nat → Nat → Nat)
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime
      scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime : Nat → Nat)
    (bound : Nat → ExecutionCost) (routeWidth fuel callerTickTime inputTime outputTime optionalTime : Nat → Nat)
    (hCallerWork : PolynomiallyBounded (fun n => (bound n).work))
    (hCallerQueries : PolynomiallyBounded (fun n => (bound n).queries))
    (hRoute : PolynomiallyBounded routeWidth) (hFuel : PolynomiallyBounded fuel)
    (hCallerTick : PolynomiallyBounded callerTickTime)
    (hInput : PolynomiallyBounded inputTime) (hOutput : PolynomiallyBounded outputTime)
    (hOptional : PolynomiallyBounded optionalTime)
    (hOverhead : PolynomialOverhead overhead)
    (hWork : PolynomiallyBounded fieldWork) (hVisits : PolynomiallyBounded fieldVisits)
    (hQueries : PolynomiallyBounded fieldQueries)
    (hNonzeroWork : PolynomiallyBounded nonzeroWork) (hNonzeroVisits : PolynomiallyBounded nonzeroVisits)
    (hNonzeroQueries : PolynomiallyBounded nonzeroQueries) (hSourceWidth : PolynomiallyBounded sourceWidth)
    (hTapeWidth : PolynomiallyBounded tapeWidth) (hSaved : PolynomiallyBounded savedCap)
    (hRemaining : PolynomiallyBounded remainingCap) (hTick : PolynomiallyBounded tickTime)
    (hCompare : PolynomiallyBounded comparisonTime) (hZero : PolynomiallyBounded zeroTime)
    (hAdd : PolynomiallyBounded addTime) (hRequest : PolynomiallyBounded requestTime)
    (hResponse : PolynomiallyBounded responseTime) (hQuery : PolynomiallyBounded queryTime)
    (hArity : PolynomiallyBounded arityTime) (hReply : PolynomiallyBounded replyTime)
    (hWidth : PolynomiallyBounded width) (hManaged : PolynomiallyBounded managedCap)
    (hLive : PolynomiallyBounded liveCap) (hMessage : PolynomiallyBounded messageTime)
    (hPoint : PolynomiallyBounded pointTime) (hScale : PolynomiallyBounded scaleTime)
    (hSub : PolynomiallyBounded subTime)
    (hGroupZero : PolynomiallyBounded groupZeroTime) (hScalarAdd : PolynomiallyBounded scalarAddTime) (hPort : PolynomiallyBounded portWidth)
    (hEncode : PolynomiallyBounded encodeTime) (hTag : PolynomiallyBounded tagTime) :
    PolynomiallyBounded (fun n => timeBudget (overhead n)
      (frameWidth (width n) (managedCap n) (liveCap n) (routeWidth n))
      (ListROM.NativeHandler.callerTime (overhead n) (routeWidth n) (fuel n)
        ((bound n).work + 2 * (bound n).queries + 2) (fun _ => (bound n).queries)
        (NativeHandler.timeBudget (overhead n) (fieldWork n) (fieldVisits n) (fieldQueries n)
          (nonzeroWork n) (nonzeroVisits n) (nonzeroQueries n) (sourceWidth n)
          (tapeWidth n) (savedCap n) (remainingCap n) (tickTime n) (comparisonTime n) (zeroTime n)
          (addTime n) (requestTime n) (responseTime n) (queryTime n) (arityTime n) (replyTime n)
          (width n) (managedCap n) (liveCap n) (messageTime n) (pointTime n) (scaleTime n) (subTime n)
          (groupZeroTime n) (scalarAddTime n) (portWidth n) (encodeTime n) (tagTime n)) (callerTickTime n))
      (finalHashTime (overhead n) (fieldWork n) (fieldVisits n) (fieldQueries n) (tapeWidth n) (savedCap n)
        (remainingCap n) (tickTime n) (comparisonTime n) (zeroTime n) (queryTime n) (width n)
        (liveCap n) (messageTime n) (pointTime n)) (inputTime n) (outputTime n) (optionalTime n)) := by
  have hcaller := NativeHandler.callerResourcesTime_polynomial overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth
    savedCap remainingCap tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime
    replyTime width managedCap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime
    bound routeWidth fuel callerTickTime hCallerWork hCallerQueries hRoute hFuel hCallerTick hOverhead
    hWork hVisits hQueries hNonzeroWork hNonzeroVisits hNonzeroQueries hSourceWidth hTapeWidth hSaved hRemaining hTick hCompare hZero hAdd hRequest hResponse
    hQuery hArity hReply hWidth hManaged hLive hMessage hPoint hScale hSub hGroupZero hScalarAdd hPort hEncode hTag
  have hfinal := finalHashTime_polynomial overhead fieldWork fieldVisits fieldQueries tapeWidth savedCap remainingCap tickTime
    comparisonTime zeroTime queryTime width liveCap messageTime pointTime hOverhead hWork hVisits hQueries
    hTapeWidth hSaved hRemaining hTick hCompare hZero hQuery hWidth hLive hMessage hPoint
  exact timeBudget_polynomial overhead _ _ _ inputTime outputTime optionalTime hOverhead
    (frameWidth_polynomial width managedCap liveCap routeWidth hWidth hManaged hLive hRoute)
    hcaller hfinal hInput hOutput hOptional

end Signatures.Runtime.Schnorr.NonzeroListROM.NativePass
