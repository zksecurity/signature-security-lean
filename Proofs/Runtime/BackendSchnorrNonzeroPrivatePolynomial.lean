import Proofs.Runtime.BackendSchnorrNonzeroPrivateBudget

/-! Polynomial growth of the installed nonzero signer from original sampler,
primitive and interface resources. No completed sampler/wrapper bound is assumed. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroListROM.NativeSigning

open BackendProgram RawTape

/-- Numeric form of the actual code budget, independent of represented types. -/
def codeDescription (allowance : Nat) (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (requestSize responseSize aritySize replySize fieldSize nonzeroSize : Nat) : Nat :=
  let raw := Expression.descriptionBound allowance primitiveSize NativeUniform.prepareExpression +
    Expression.descriptionBound allowance primitiveSize NativeUniform.hitExpression +
    Expression.descriptionBound allowance primitiveSize NativeUniform.saveExpression +
    requestSize + responseSize + 14 * allowance + 12
  let handler := raw + aritySize + replySize + 14 * allowance + 11
  (handler + 18 * allowance + 6) * (2 * fieldSize + nonzeroSize) +
    NonzeroSigning.Native.description allowance primitiveSize

theorem runtimeBound_polynomial (overhead : Nat → Nat → Nat)
    (fieldWork fieldVisits fieldQueries nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth savedCap
      remainingCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
      width cap messageTime pointTime scaleTime subTime groupZeroTime scalarAddTime : Nat → Nat)
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
    (hMessageTime : PolynomiallyBounded messageTime)
    (hPointTime : PolynomiallyBounded pointTime)
    (hScaleTime : PolynomiallyBounded scaleTime)
    (hSubTime : PolynomiallyBounded subTime)
    (hGroupZeroTime : PolynomiallyBounded groupZeroTime)
    (hScalarAddTime : PolynomiallyBounded scalarAddTime)
    : PolynomiallyBounded (fun n => runtimeBound (overhead n)
      (fieldWork n) (fieldVisits n) (fieldQueries n) (nonzeroWork n) (nonzeroVisits n) (nonzeroQueries n) (sourceWidth
        n) (tapeWidth n) (savedCap n) (remainingCap n) (tickTime n) (comparisonTime n) (zeroTime n) (natAddTime n)
        (requestTime n) (responseTime n) (queryTime n) (arityTime n) (replyTime n) (width n) (cap n) (messageTime n)
        (pointTime n) (scaleTime n) (subTime n) (groupZeroTime n) (scalarAddTime n)) := by
  have hFirst := NativePrivate.samplerTime_polynomial overhead fieldWork fieldVisits fieldQueries sourceWidth tapeWidth
    savedCap remainingCap tickTime comparisonTime zeroTime natAddTime requestTime responseTime queryTime arityTime replyTime
    hOverhead hFieldWork hFieldVisits hFieldQueries hSourceWidth hTapeWidth hSavedCap hRemainingCap hTickTime hComparisonTime
    hZeroTime hNatAddTime hRequestTime hResponseTime hQueryTime hArityTime hReplyTime
  have hSecond := NativePrivate.samplerTime_polynomial overhead fieldWork fieldVisits fieldQueries sourceWidth tapeWidth
    (fun n => savedCap n + fieldQueries n) remainingCap tickTime comparisonTime zeroTime natAddTime
    requestTime responseTime queryTime arityTime replyTime hOverhead hFieldWork hFieldVisits hFieldQueries hSourceWidth
    hTapeWidth (hSavedCap.add hFieldQueries) hRemainingCap hTickTime hComparisonTime hZeroTime hNatAddTime
    hRequestTime hResponseTime hQueryTime hArityTime hReplyTime
  have hThird := NativePrivate.samplerTime_polynomial overhead nonzeroWork nonzeroVisits nonzeroQueries sourceWidth tapeWidth
    (fun n => savedCap n + 2 * fieldQueries n) remainingCap tickTime comparisonTime zeroTime natAddTime
    requestTime responseTime queryTime arityTime replyTime hOverhead hNonzeroWork hNonzeroVisits hNonzeroQueries hSourceWidth
    hTapeWidth (hSavedCap.add ((PolynomiallyBounded.const 2).mul hFieldQueries)) hRemainingCap hTickTime
    hComparisonTime hZeroTime hNatAddTime hRequestTime hResponseTime hQueryTime hArityTime hReplyTime
  exact NonzeroSigning.Native.signingTime_polynomial overhead width cap messageTime pointTime scaleTime subTime
    groupZeroTime scalarAddTime _ _ _ hOverhead hWidth hCap hMessageTime hPointTime hScaleTime hSubTime
    hGroupZeroTime hScalarAddTime hFirst hSecond hThird

theorem codeDescription_polynomial (allowance : Nat → Nat)
    (primitiveSize : Nat → {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (requestSize responseSize aritySize replySize fieldSize nonzeroSize : Nat → Nat)
    (hAllowance : PolynomiallyBounded allowance)
    (hPrimitive : ∀ {a b} (op : CryptoOp a b), PolynomiallyBounded (fun n => primitiveSize n op))
    (hRequest : PolynomiallyBounded requestSize) (hResponse : PolynomiallyBounded responseSize)
    (hArity : PolynomiallyBounded aritySize) (hReply : PolynomiallyBounded replySize)
    (hField : PolynomiallyBounded fieldSize) (hNonzero : PolynomiallyBounded nonzeroSize) :
    PolynomiallyBounded (fun n => codeDescription (allowance n) (primitiveSize n)
      (requestSize n) (responseSize n) (aritySize n) (replySize n) (fieldSize n) (nonzeroSize n)) := by
  have expressionPoly {Γ a} (e : Expr CryptoOp Γ a) :
      PolynomiallyBounded (fun n => Expression.descriptionBound (allowance n) (primitiveSize n) e) :=
    Expression.descriptionBound_polynomial allowance primitiveSize hAllowance hPrimitive e
  have programPoly := Language.descriptionBound_polynomial allowance primitiveSize (fun _ _ => 0)
    hAllowance hPrimitive (fun _ => PolynomiallyBounded.const 0)
    (NonzeroSigning.body NonzeroSigning.Native.Draw.field NonzeroSigning.Native.Draw.nonzero)
  unfold codeDescription NonzeroSigning.Native.description
  repeat' first
    | assumption
    | apply expressionPoly
    | apply PolynomiallyBounded.add
    | apply PolynomiallyBounded.mul
    | apply PolynomiallyBounded.const

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [QD : Q.IsDistributive]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (uniform : UniformSampling.Ports (Q := Q) rep.data (iface := iface))
  (ports : NativePrivate.Ports (Q := Q) rep (iface := iface))
  (fieldSampler nonzeroSampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

/-- The polynomial numeric formula bounds the actual compiled program. -/
theorem code_description_of_inputs (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (distribution : ∀ {A B T : Type} (a : C.Str A) (b : C.Str B) (t : C.Str T),
      sizes.localSize (QD.distribute a b t) ≤ allowance) :
    (code rep data cost primitive uniform ports fieldSampler nonzeroSampler).descriptionSize sizes ≤
      codeDescription allowance (fun op => sizes.localSize (primitive op))
        (sizes.localSize uniform.request) (sizes.localSize uniform.response)
        (sizes.localSize ports.arity) (sizes.localSize ports.reply)
        (fieldSampler.descriptionSize sizes) (nonzeroSampler.descriptionSize sizes) :=
  code_description rep data cost primitive uniform ports fieldSampler nonzeroSampler sizes allowance laws dataLaws distribution

end Signatures.Runtime.Schnorr.NonzeroListROM.NativeSigning
