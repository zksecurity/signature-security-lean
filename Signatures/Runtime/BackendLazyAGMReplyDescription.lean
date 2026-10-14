import Signatures.Runtime.BackendLazyAGMReply

/-! Stored-code bounds for the actual lazy AGM hash/sign reply programs.
Both routing stages, all scalar/group instruction occurrences, the list cache,
and every stored scalar sampler are counted. Transcript/cache data sizes and
execution budgets are separate obligations.
-/

open OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F] [SampleableType F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

omit [SampleableType F] in
theorem replyBody_description {value config : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, storeTy value config] value)
    (response : Expr CryptoOp [value, config] point₁) (signing : Bool) :
    (replyBody rep data cost primitive sampler fallback response signing).descriptionSize sizes ≤
      sampler.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) fallback +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) response +
        352 * allowance + 34 := by
  have ha := Expression.arguments_size rep data (arithmetic F G₁ G₂ M M cost) primitive
    sizes allowance laws dataLaws (fun instr => sizes.localSize (primitive instr))
    (fun _ => le_rfl) (cacheArgs fallback)
  rw [cacheArgs_description] at ha
  have hi := laws.pair_bound ha (laws.identity (rep.env [message, storeTy value config]))
  have hc := SampledCache.description rep data (arithmetic F G₁ G₂ M M cost) primitive
    (rep.env [message, storeTy value config]) sampler CryptoOp.messageEq sizes allowance laws dataLaws
  have ho := Expression.compile_size rep data (arithmetic F G₁ G₂ M M cost) primitive
    sizes allowance laws dataLaws (fun instr => sizes.localSize (primitive instr))
    (fun _ => le_rfl) (replyResult signing response)
  rw [replyResult_description] at ho
  rw [replyBody]
  dsimp only [Code.descriptionSize]
  omega

omit [SampleableType F] in
theorem backendReply_description {value config : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, storeTy value config] value)
    (response : Expr CryptoOp [value, config] point₁) (signing : Bool) :
    (backendReply rep data cost primitive sampler fallback response signing).descriptionSize sizes ≤
      sampler.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) fallback +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) response +
        357 * allowance + 36 := by
  have hb := replyBody_description rep data cost primitive sizes allowance laws dataLaws
    sampler fallback response signing
  have hi := laws.pair_bound (laws.fst (rep.ty message) (rep.ty (storeTy value config)))
    (laws.pair_bound (laws.snd (rep.ty message) (rep.ty (storeTy value config)))
      (dataLaws.unit (rep.ty (.pair message (storeTy value config)))))
  rw [backendReply]
  dsimp only [Code.descriptionSize, replyFrame]
  omega

theorem backendGoodReply_description (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
    (signing : Bool) :
    (backendGoodReply rep data cost primitive samplingCode signing).descriptionSize sizes ≤
      samplingCode.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        sizes.localSize (primitive .zero) + sizes.localSize (primitive .scale₁) + 400 * allowance + 40 := by
  rw [backendGoodReply]
  have h := backendReply_description rep data cost primitive sizes allowance laws dataLaws
    samplingCode.scalar (.op .zero .unit) (goodResponse signing) signing
  rw [goodResponse_description] at h
  simp only [Expression.descriptionBound] at h
  omega

theorem backendBadReply_description (samplingCode : MachineCompiler.SamplingImplementation Q iface rep)
    (signing : Bool) :
    (backendBadReply rep data cost primitive samplingCode signing).descriptionSize sizes ≤
      2 * samplingCode.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        2 * sizes.localSize (primitive .zero) + 3 * sizes.localSize (primitive .scale₁) +
        sizes.localSize (primitive .add₁) + 450 * allowance + 50 := by
  rw [backendBadReply]
  have h := backendReply_description rep data cost primitive sizes allowance laws dataLaws
    (pairSampler rep data samplingCode) (.pair (.op .zero .unit) (.op .zero .unit)) (badResponse signing) signing
  have hs := PairSampling.description rep.data data (rep.ty scalar) (rep.ty scalar)
    samplingCode.scalar samplingCode.scalar sizes allowance laws dataLaws
  change (pairSampler rep data samplingCode).descriptionSize sizes ≤ _ at hs
  rw [badResponse_description] at h
  cases signing <;> simp only [Expression.descriptionBound, Bool.false_eq_true, ite_false, ite_true] at h <;> omega

end Signatures.Runtime.LazyAGM
