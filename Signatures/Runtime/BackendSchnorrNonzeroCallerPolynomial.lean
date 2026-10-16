import Signatures.Runtime.BackendSchnorrNonzeroCallerResources
import Signatures.Runtime.BackendSchnorrNonzeroHandlerPolynomial
import Signatures.Runtime.BackendSchnorrROMCallerPolynomial

/-! Polynomial closure of complete nonzero-nonce caller execution from the
attacker's original work/queries and both original sampler resource families. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler

open ListROM.NativeHandler

theorem callerResourcesTime_polynomial (overhead : Nat → Nat → Nat)
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime
      scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime : Nat → Nat)
    (bound : Nat → ExecutionCost) (routeWidth fuel callerTickTime : Nat → Nat)
    (hCallerWork : PolynomiallyBounded (fun n => (bound n).work))
    (hCallerQueries : PolynomiallyBounded (fun n => (bound n).queries))
    (hRoute : PolynomiallyBounded routeWidth) (hFuel : PolynomiallyBounded fuel)
    (hCallerTick : PolynomiallyBounded callerTickTime)
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
    PolynomiallyBounded (fun n => callerTime (overhead n) (routeWidth n) (fuel n)
      ((bound n).work + 2 * (bound n).queries + 2) (fun _ => (bound n).queries)
      (timeBudget (overhead n) (fieldWork n) (fieldVisits n) (fieldQueries n)
        (nonzeroWork n) (nonzeroVisits n) (nonzeroQueries n) (sourceWidth n) (tapeWidth n) (savedCap n)
        (remainingCap n) (tickTime n) (comparisonTime n) (zeroTime n) (addTime n) (requestTime n)
        (responseTime n) (queryTime n) (arityTime n) (replyTime n) (width n) (managedCap n) (liveCap n)
        (messageTime n) (pointTime n) (scaleTime n) (subTime n) (groupZeroTime n) (scalarAddTime n) (portWidth n) (encodeTime n) (tagTime n))
      (callerTickTime n)) := by
  have hHandler := timeBudget_polynomial overhead fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap
    tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime width managedCap
    liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime hOverhead hWork hVisits hQueries hNonzeroWork hNonzeroVisits hNonzeroQueries
    hSourceWidth hTapeWidth hSaved hRemaining hTick hCompare hZero hAdd hRequest hResponse hQuery hArity hReply
    hWidth hManaged hLive hMessage hPoint hScale hSub hGroupZero hScalarAdd hPort hEncode hTag
  exact callerTime_polynomial overhead routeWidth fuel _ _ callerTickTime _ hOverhead hRoute hFuel
    ((hCallerWork.add ((PolynomiallyBounded.const 2).mul hCallerQueries)).add (PolynomiallyBounded.const 2))
    hHandler hCallerTick (fun _ => hCallerQueries)

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler
