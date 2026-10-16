import Signatures.Runtime.BackendSchnorrNonzeroHandlerBudget
import Signatures.Runtime.BackendSchnorrNonzeroComponentsPolynomial
import Signatures.Runtime.BackendSchnorrROMHandlerPolynomial

/-! Polynomial closure of the full nonzero dispatcher from original sampler,
primitive and encoding resources, without a polynomial numeric-arity bound. -/

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler

open ListROM.NativeHandler

theorem timeBudget_polynomial (overhead : Nat → Nat → Nat)
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime
      scaleTime subTime groupZeroTime scalarAddTime portWidth encodeTime tagTime : Nat → Nat)
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
    PolynomiallyBounded (fun n => timeBudget (overhead n) (fieldWork n) (fieldVisits n) (fieldQueries n)
      (nonzeroWork n) (nonzeroVisits n) (nonzeroQueries n)
      (sourceWidth n) (tapeWidth n) (savedCap n) (remainingCap n) (tickTime n) (comparisonTime n)
      (zeroTime n) (addTime n) (requestTime n) (responseTime n) (queryTime n) (arityTime n) (replyTime n)
      (width n) (managedCap n) (liveCap n) (messageTime n) (pointTime n) (scaleTime n) (subTime n)
      (groupZeroTime n) (scalarAddTime n) (portWidth n) (encodeTime n) (tagTime n)) := by
  obtain ⟨_, hHash, _⟩ := ListROM.NativeComponents.cache_components_polynomial overhead fieldWork fieldVisits fieldQueries
    sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime requestTime
    responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime scaleTime subTime
    hOverhead hWork hVisits hQueries hSourceWidth hTapeWidth hSaved hRemaining hTick hCompare hZero hAdd
    hRequest hResponse hQuery hArity hReply hWidth hManaged hLive hMessage hPoint hScale hSub
  have hRandom := ListROM.NativeComponents.randomTime_polynomial overhead width tapeWidth managedCap liveCap savedCap
    remainingCap comparisonTime zeroTime addTime requestTime responseTime queryTime hOverhead hWidth hTapeWidth
    hManaged hLive hSaved hRemaining hCompare hZero hAdd hRequest hResponse hQuery
  have hSign := NativeComponents.signingTime_polynomial overhead fieldWork fieldVisits fieldQueries
    nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime
    zeroTime addTime requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime
    pointTime scaleTime subTime groupZeroTime scalarAddTime hOverhead hWork hVisits hQueries hNonzeroWork hNonzeroVisits
    hNonzeroQueries hSourceWidth hTapeWidth hSaved hRemaining hTick hCompare hZero hAdd hRequest hResponse hQuery
    hArity hReply hWidth hManaged hLive hMessage hPoint hScale hSub hGroupZero hScalarAdd
  unfold timeBudget
  apply handlerTime_polynomial overhead _ _ _ _ encodeTime tagTime hOverhead ?_ hRandom hHash hSign hEncode hTag
  unfold ListROM.NativeHandler.frameWidth ListROM.NativeComponents.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeHandler
