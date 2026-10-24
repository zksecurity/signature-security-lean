import Proofs.Runtime.BackendSchnorrROMCallerResources
import Proofs.Runtime.BackendSchnorrROMHandlerPolynomial

/-! Polynomial closure of complete caller execution, including the original
attacker work, all dispatcher calls, initialization and loop control. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

theorem callerTime_polynomial (overhead : Nat → Nat → Nat)
    (routeWidth fuel localTime handlerTime tickTime : Nat → Nat) (queries : Fin 3 → Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded routeWidth)
    (hFuel : PolynomiallyBounded fuel) (hLocal : PolynomiallyBounded localTime)
    (hHandler : PolynomiallyBounded handlerTime) (hTick : PolynomiallyBounded tickTime)
    (hQueries : ∀ k, PolynomiallyBounded (queries k)) :
    PolynomiallyBounded (fun n => callerTime (overhead n) (routeWidth n) (fuel n) (localTime n)
      (fun k => queries k n) (handlerTime n) (tickTime n)) := by
  have hsum := PolynomiallyBounded.sum (fun k n => queries k n * handlerTime n)
    (fun k => (hQueries k).mul hHandler)
  unfold callerTime
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

theorem callerResourcesTime_polynomial (overhead : Nat → Nat → Nat)
    (work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime
      scaleTime subTime portWidth encodeTime tagTime : Nat → Nat)
    (bound : Nat → ExecutionCost) (routeWidth fuel callerTickTime : Nat → Nat)
    (hCallerWork : PolynomiallyBounded (fun n => (bound n).work))
    (hCallerQueries : PolynomiallyBounded (fun n => (bound n).queries))
    (hRoute : PolynomiallyBounded routeWidth) (hFuel : PolynomiallyBounded fuel)
    (hCallerTick : PolynomiallyBounded callerTickTime)
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
    PolynomiallyBounded (fun n => callerTime (overhead n) (routeWidth n) (fuel n)
      ((bound n).work + 2 * (bound n).queries + 2) (fun _ => (bound n).queries)
      (timeBudget (overhead n) (work n) (visits n) (queries n) (sourceWidth n) (tapeWidth n) (savedCap n)
        (remainingCap n) (tickTime n) (comparisonTime n) (zeroTime n) (addTime n) (requestTime n)
        (responseTime n) (queryTime n) (arityTime n) (replyTime n) (width n) (managedCap n) (liveCap n)
        (messageTime n) (pointTime n) (scaleTime n) (subTime n) (portWidth n) (encodeTime n) (tagTime n))
      (callerTickTime n)) := by
  have hHandler := timeBudget_polynomial overhead work visits queries sourceWidth tapeWidth savedCap remainingCap
    tickTime comparisonTime zeroTime addTime requestTime responseTime queryTime arityTime replyTime width managedCap
    liveCap messageTime pointTime scaleTime subTime portWidth encodeTime tagTime hOverhead hWork hVisits hQueries
    hSourceWidth hTapeWidth hSaved hRemaining hTick hCompare hZero hAdd hRequest hResponse hQuery hArity hReply
    hWidth hManaged hLive hMessage hPoint hScale hSub hPort hEncode hTag
  exact callerTime_polynomial overhead routeWidth fuel _ _ callerTickTime _ hOverhead hRoute hFuel
    ((hCallerWork.add ((PolynomiallyBounded.const 2).mul hCallerQueries)).add (PolynomiallyBounded.const 2))
    hHandler hCallerTick (fun _ => hCallerQueries)

end Signatures.Runtime.Schnorr.ListROM.NativeHandler
