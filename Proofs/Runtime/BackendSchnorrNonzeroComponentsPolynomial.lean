import Proofs.Runtime.BackendSchnorrNonzeroComponentsBudget

/-! Polynomial runtime and code of shared-store nonzero signing from original
sampler work/queries, primitive prices, widths and primitive/port descriptions. -/

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeComponents

open BackendProgram

theorem signingTime_polynomial (overhead : Nat → Nat → Nat)
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap
      remainingCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
      width cap liveCap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead)
    (hFieldWork : PolynomiallyBounded fieldWork)
    (hFieldVisits : PolynomiallyBounded fieldVisits)
    (hFieldQueries : PolynomiallyBounded fieldQueries)
    (hNonzeroWork : PolynomiallyBounded nonzeroWork)
    (hNonzeroVisits : PolynomiallyBounded nonzeroVisits)
    (hNonzeroQueries : PolynomiallyBounded nonzeroQueries)
    (hSourceWidth : PolynomiallyBounded sourceWidth)
    (hTapeWidth : PolynomiallyBounded tapeWidth)
    (hSavedCap : PolynomiallyBounded savedCap)
    (hRemainingCap : PolynomiallyBounded remainingCap)
    (hTickTime : PolynomiallyBounded tickTime)
    (hComparisonTime : PolynomiallyBounded comparisonTime)
    (hZeroTime : PolynomiallyBounded zeroTime)
    (hNatAddTime : PolynomiallyBounded natAddTime)
    (hRequestTime : PolynomiallyBounded requestTime)
    (hResponseTime : PolynomiallyBounded responseTime)
    (hQueryTime : PolynomiallyBounded queryTime)
    (hArityTime : PolynomiallyBounded arityTime)
    (hReplyTime : PolynomiallyBounded replyTime)
    (hWidth : PolynomiallyBounded width)
    (hCap : PolynomiallyBounded cap)
    (hLiveCap : PolynomiallyBounded liveCap)
    (hMessageTime : PolynomiallyBounded messageTime)
    (hPointTime : PolynomiallyBounded pointTime)
    (hScaleTime : PolynomiallyBounded scaleTime)
    (hSubTime : PolynomiallyBounded subTime)
    (hGroupZeroTime : PolynomiallyBounded groupZeroTime)
    (hScalarAddTime : PolynomiallyBounded scalarAddTime)
    : PolynomiallyBounded (fun n => signingTime (overhead n)
      (fieldWork n) (fieldVisits n) (fieldQueries n) (nonzeroWork n) (nonzeroVisits n) (nonzeroQueries n) (sourceWidth
        n) (tapeWidth n) (savedCap n) (remainingCap n) (tickTime n) (comparisonTime n) (zeroTime n) (natAddTime n)
        (requestTime n) (responseTime n) (queryTime n) (arityTime n) (replyTime n) (width n) (cap n) (liveCap n)
        (messageTime n) (pointTime n) (scaleTime n) (subTime n) (groupZeroTime n) (scalarAddTime n)) := by
  have hCore := NativeSigning.runtimeBound_polynomial overhead
    fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap
      remainingCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
      width cap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime
    hOverhead hFieldWork hFieldVisits hFieldQueries hNonzeroWork hNonzeroVisits hNonzeroQueries hSourceWidth hTapeWidth
      hSavedCap hRemainingCap hTickTime hComparisonTime hZeroTime hNatAddTime hRequestTime hResponseTime hQueryTime
      hArityTime hReplyTime hWidth hCap hMessageTime hPointTime hScaleTime hSubTime hGroupZeroTime hScalarAddTime
  unfold signingTime ListROM.NativeComponents.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

theorem signingDescription_polynomial (allowance : Nat → Nat)
    (primitiveSize : Nat → {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (requestSize responseSize aritySize replySize fieldSize nonzeroSize : Nat → Nat)
    (hAllowance : PolynomiallyBounded allowance)
    (hPrimitive : ∀ {a b} (op : CryptoOp a b), PolynomiallyBounded (fun n => primitiveSize n op))
    (hRequest : PolynomiallyBounded requestSize) (hResponse : PolynomiallyBounded responseSize)
    (hArity : PolynomiallyBounded aritySize) (hReply : PolynomiallyBounded replySize)
    (hField : PolynomiallyBounded fieldSize) (hNonzero : PolynomiallyBounded nonzeroSize) :
    PolynomiallyBounded (fun n => NativeSigning.codeDescription (allowance n) (primitiveSize n)
      (requestSize n) (responseSize n) (aritySize n) (replySize n) (fieldSize n) (nonzeroSize n) + 1024 * allowance n + 8) :=
  ((NativeSigning.codeDescription_polynomial allowance primitiveSize requestSize responseSize aritySize replySize
    fieldSize nonzeroSize hAllowance hPrimitive hRequest hResponse hArity hReply hField hNonzero).add
      ((PolynomiallyBounded.const 1024).mul hAllowance)).add (PolynomiallyBounded.const 8)

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeComponents
