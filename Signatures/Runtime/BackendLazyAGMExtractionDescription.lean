import Signatures.Runtime.BackendLazyAGMExtraction
import Signatures.Runtime.BackendLazyAGMReadDescription
import Signatures.Runtime.BackendWeakeningSize

/-! Stored-code bounds for both complete native lazy extractors. They count
all stored row-evaluation bodies, private caches/samplers, coefficient matching,
default construction, target access, and final field arithmetic. Counts do not
depend on transcript or message-universe cardinality. Runtime is separate. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

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
  (sampling : MachineCompiler.SamplingImplementation Q iface rep)
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

theorem backendExtractGood_description :
    (backendExtractGood rep data cost primitive sampling).descriptionSize sizes ≤
      3 * sampling.scalar.descriptionSize sizes + 3 * sizes.localSize (primitive .messageEq) +
        8 * sizes.localSize (primitive .zero) + sizes.localSize (primitive .zero₁) +
        4 * sizes.localSize (primitive .natEq) + 4 * sizes.localSize (primitive .natSub) +
        6 * sizes.localSize (primitive .natAdd) + 3 * sizes.localSize (primitive .add) +
        2 * sizes.localSize (primitive .mul) + sizes.localSize (primitive .sub) +
        sizes.localSize (primitive .div) + 8192 * allowance + 512 := by
  have hr := backendGoodRead_description rep data cost primitive sizes allowance laws dataLaws sampling
  rw [backendGoodRead] at hr
  rw [backendExtractGood]
  have h := Language.compile_descriptionSize sizes allowance laws rep data
    (arithmetic F G₁ G₂ M M cost) primitive dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (rep.ty (cacheTy scalar)) (readEffect rep data cost primitive sampling.scalar (.op .zero .unit))
    (fun _ => sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
      sizes.localSize (primitive .zero) + 300 * allowance + 40)
    (fun instr => by cases instr; exact hr) extractGood
  refine h.trans ?_
  simp only [extractGood, defaultRow, evaluateTokens, evaluateRows, evalBody, evalUpdate, selectRow,
    goodCombine, listLength, Language.descriptionBound, Expression.descriptionBound,
    Expression.descriptionBound_weakenTail, Expression.argumentsDescription,
    AGM.tokenRows, AGM.attachTable, AGM.attachFold, AGM.attachBody, reverseList, index, indexBody,
    v0, v1, v2, v3, v4, Expression.variableDescription]
  omega

theorem backendExtractBad_description :
    (backendExtractBad rep data cost primitive sampling).descriptionSize sizes ≤
      4 * sampling.scalar.descriptionSize sizes + 2 * sizes.localSize (primitive .messageEq) +
        8 * sizes.localSize (primitive .zero) + sizes.localSize (primitive .zero₁) +
        2 * sizes.localSize (primitive .natEq) + 2 * sizes.localSize (primitive .natSub) +
        3 * sizes.localSize (primitive .natAdd) + 2 * sizes.localSize (primitive .add) +
        2 * sizes.localSize (primitive .mul) + 2 * sizes.localSize (primitive .sub) +
        sizes.localSize (primitive .neg) + sizes.localSize (primitive .div) +
        8192 * allowance + 512 := by
  have hr := backendBadRead_description rep data cost primitive sizes allowance laws dataLaws sampling
  rw [backendBadRead] at hr
  rw [backendExtractBad]
  have h := Language.compile_descriptionSize sizes allowance laws rep data
    (arithmetic F G₁ G₂ M M cost) primitive dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (rep.ty (cacheTy (.pair scalar scalar)))
    (readEffect rep data cost primitive (pairSampler rep data sampling)
      (.pair (.op .zero .unit) (.op .zero .unit)))
    (fun _ => 2 * sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
      2 * sizes.localSize (primitive .zero) + 320 * allowance + 48)
    (fun instr => by cases instr; exact hr) extractBad
  refine h.trans ?_
  simp only [extractBad, defaultRow, evaluateTokens, evaluateRows, evalBody, evalUpdate, selectRow,
    badCombine, listLength, Language.descriptionBound, Expression.descriptionBound,
    Expression.descriptionBound_weakenTail, Expression.argumentsDescription,
    AGM.tokenRows, AGM.attachTable, AGM.attachFold, AGM.attachBody, reverseList, index, indexBody,
    v0, v1, v2, v3, Expression.variableDescription]
  omega

end Signatures.Runtime.LazyAGM
