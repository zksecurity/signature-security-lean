import Proofs.Runtime.BackendSchnorrROMHandlerBudget

/-! Polynomial closure for the complete executed ROM dispatcher. The numeric
size of a random sampling domain and the message-domain cardinality do not enter
the bound; encoded widths, actual query counts and primitive costs do. -/

namespace Signatures.Runtime.Schnorr.ListROM.NativeHandler

private theorem max_polynomial {f g : Nat → Nat}
    (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => max (f n) (g n)) :=
  (hf.add hg).of_le (fun _ => Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩)

theorem handlerTime_polynomial (overhead : Nat → Nat → Nat)
    (width randomTime hashTime signingTime requestTime tagTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hRandom : PolynomiallyBounded randomTime) (hHash : PolynomiallyBounded hashTime)
    (hSigning : PolynomiallyBounded signingTime) (hRequest : PolynomiallyBounded requestTime)
    (hTag : PolynomiallyBounded tagTime) :
    PolynomiallyBounded (fun n => handlerTime (overhead n) (width n) (randomTime n)
      (hashTime n) (signingTime n) (requestTime n) (tagTime n)) := by
  unfold handlerTime
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply max_polynomial
    | apply hOverhead.apply
    | apply PolynomiallyBounded.const

theorem timeBudget_polynomial (overhead : Nat → Nat → Nat)
    (work visits queries sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime
      requestTime responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime
      scaleTime subTime portWidth encodeTime tagTime : Nat → Nat)
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
    PolynomiallyBounded (fun n => timeBudget (overhead n) (work n) (visits n) (queries n)
      (sourceWidth n) (tapeWidth n) (savedCap n) (remainingCap n) (tickTime n) (comparisonTime n)
      (zeroTime n) (addTime n) (requestTime n) (responseTime n) (queryTime n) (arityTime n) (replyTime n)
      (width n) (managedCap n) (liveCap n) (messageTime n) (pointTime n) (scaleTime n) (subTime n)
      (portWidth n) (encodeTime n) (tagTime n)) := by
  obtain ⟨_, hHash, hSign⟩ := NativeComponents.cache_components_polynomial overhead work visits queries
    sourceWidth tapeWidth savedCap remainingCap tickTime comparisonTime zeroTime addTime requestTime
    responseTime queryTime arityTime replyTime width managedCap liveCap messageTime pointTime scaleTime subTime
    hOverhead hWork hVisits hQueries hSourceWidth hTapeWidth hSaved hRemaining hTick hCompare hZero hAdd
    hRequest hResponse hQuery hArity hReply hWidth hManaged hLive hMessage hPoint hScale hSub
  have hRandom := NativeComponents.randomTime_polynomial overhead width tapeWidth managedCap liveCap savedCap
    remainingCap comparisonTime zeroTime addTime requestTime responseTime queryTime hOverhead hWidth hTapeWidth
    hManaged hLive hSaved hRemaining hCompare hZero hAdd hRequest hResponse hQuery
  unfold timeBudget
  apply handlerTime_polynomial overhead _ _ _ _ encodeTime tagTime hOverhead ?_ hRandom hHash hSign hEncode hTag
  unfold frameWidth NativeComponents.frameWidth
  repeat' first
    | assumption
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

end Signatures.Runtime.Schnorr.ListROM.NativeHandler
