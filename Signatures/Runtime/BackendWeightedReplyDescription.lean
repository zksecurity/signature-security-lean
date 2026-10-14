import Signatures.Runtime.BackendWeightedReply
import Signatures.Runtime.BackendWeightedEvaluateDescription
import Signatures.Runtime.WeightedTermsDescription

/-! Complete stored-code bounds for the actual weighted hash/sign replies.
Term generation is charged in the numerical degree/dimension. Evaluation loops
store one body, and all sampler, fallback, response and transcript code is counted. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM

open BackendProgram

def Index.termsDescription (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) : Index → Nat
  | .oops d => Terms.oopsDescription allowance primitiveSize d
  | .proximity ell => Terms.proximityDescription allowance primitiveSize ell

theorem Index.terms_description (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) (index : Index) :
    Expression.descriptionBound allowance primitiveSize index.terms ≤
      index.termsDescription allowance primitiveSize := by
  cases index with
  | oops d => exact Terms.oops_description allowance primitiveSize d
  | proximity ell => exact Terms.proximity_description allowance primitiveSize ell

theorem Index.default_description (allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) (index : Index) :
    Expression.descriptionBound allowance primitiveSize index.defaultTerm ≤
      primitiveSize (.finZero index.bound) + primitiveSize .zero + 9 * allowance := by
  cases index <;> simp only [Index.defaultTerm, Index.bound, Reply.oopsDefault,
    Reply.proximityDefault, LazyAGM.ReplySyntax.v0, Expression.descriptionBound,
    Expression.variableDescription] <;> omega

namespace Reply

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

include laws dataLaws

theorem signValue_description {indexTy messageTy value : Ty CryptoAtom}
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy))
    (evaluate : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.env [.list (Terms.termTy indexTy), Terms.termTy indexTy])
        (rep.ty (cacheTy indexTy value))) (rep.ty (cacheResultTy indexTy value))) :
    (signValue rep data cost primitive terms default evaluate).descriptionSize sizes ≤
      evaluate.descriptionSize sizes +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) terms +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) default +
        6 * allowance + 6 := by
  have hf := laws.pair_bound (laws.identity (rep.ty messageTy)) (dataLaws.unit (rep.ty messageTy))
  have ha := Expression.arguments_size rep data (arithmetic F G₁ G₂ K M cost) primitive
    sizes allowance laws dataLaws (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (signArgs terms default)
  dsimp only [signValue, messageFrame, Code.descriptionSize, signArgs, Expression.argumentsDescription] at *
  omega

theorem backendReply_description {indexTy messageTy value config : Ty CryptoAtom} (signing : Bool)
    (valueCode : Code Q unifSpec iface
      (rep.ty (.pair (requestTy indexTy messageTy signing) (cacheTy indexTy value)))
      (rep.ty (cacheResultTy indexTy value)))
    (response : Expr CryptoOp [value, config] point₁) :
    (backendReply rep data cost primitive signing valueCode response).descriptionSize sizes ≤
      valueCode.descriptionSize sizes +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) response +
        104 * allowance + 7 := by
  have hf := laws.pair_bound (laws.fst (rep.ty (requestTy indexTy messageTy signing))
      (rep.ty (storeTy indexTy messageTy value config)))
    (laws.pair_bound (laws.snd (rep.ty (requestTy indexTy messageTy signing))
      (rep.ty (storeTy indexTy messageTy value config)))
      (dataLaws.unit (rep.ty (.pair (requestTy indexTy messageTy signing) (storeTy indexTy messageTy value config)))))
  have ha := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive
    sizes allowance laws dataLaws (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (cacheArgs (indexTy := indexTy) (messageTy := messageTy) (value := value) (config := config) signing)
  rw [cacheArgs_description] at ha
  have hi := laws.pair_bound ha (laws.identity
    (rep.env [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config]))
  have ho := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive
    sizes allowance laws dataLaws (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (replyResult (indexTy := indexTy) (messageTy := messageTy) signing response)
  rw [replyResult_description] at ho
  rw [backendReply]
  dsimp only [Code.descriptionSize, replyFrame]
  omega

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

theorem goodHash_description :
    (goodHash rep data cost primitive sampling index).descriptionSize sizes ≤
      sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .keyEq) +
        2 * sizes.localSize (primitive (.finVal index.bound)) +
        1 * sizes.localSize (primitive .natEq) +
        1 * sizes.localSize (primitive .zero) +
        1 * sizes.localSize (primitive .scale₁) +
        480 * allowance + 48 := by
  rw [goodHash.eq_def]
  have hr := backendReply_description (indexTy := index.ty) (messageTy := index.messageTy) rep data cost primitive sizes allowance laws dataLaws
    false (Read.goodRead rep data cost primitive sampling index) (LazyAGM.goodResponse false)
  rw [LazyAGM.goodResponse_description] at hr
  have hv := Read.goodRead_description rep data cost primitive sizes allowance laws dataLaws sampling index
  omega

theorem goodSign_description :
    (goodSign rep data cost primitive sampling index).descriptionSize sizes ≤
      sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .keyEq) +
        2 * sizes.localSize (primitive (.finVal index.bound)) +
        2 * sizes.localSize (primitive .natEq) +
        3 * sizes.localSize (primitive .zero) +
        1 * sizes.localSize (primitive .scale₁) +
        1 * sizes.localSize (primitive .add) + 1 * sizes.localSize (primitive .mul) +
        sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) +
        sizes.localSize (primitive (.finZero index.bound)) +
        index.termsDescription allowance (fun instr => sizes.localSize (primitive instr)) +
        1280 * allowance + 160 := by
  rw [goodSign.eq_def]
  have hr := backendReply_description (indexTy := index.ty) (messageTy := index.messageTy) rep data cost primitive sizes allowance laws dataLaws
    true (goodSignValue rep data cost primitive sampling index) (LazyAGM.goodResponse true)
  rw [LazyAGM.goodResponse_description] at hr
  have hs := signValue_description rep data cost primitive sizes allowance laws dataLaws
    index.terms index.defaultTerm (Evaluate.backendGood rep data cost primitive sampling index)
  have he := Evaluate.backendGood_description rep data cost primitive sizes allowance laws dataLaws sampling index
  have ht := index.terms_description allowance (fun instr => sizes.localSize (primitive instr))
  have hd := index.default_description allowance (fun instr => sizes.localSize (primitive instr))
  change (goodSignValue rep data cost primitive sampling index).descriptionSize sizes ≤ _ at hs
  omega

theorem badHash_description :
    (badHash rep data cost primitive sampling index).descriptionSize sizes ≤
      2 * sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .keyEq) +
        2 * sizes.localSize (primitive (.finVal index.bound)) +
        1 * sizes.localSize (primitive .natEq) +
        2 * sizes.localSize (primitive .zero) +
        3 * sizes.localSize (primitive .scale₁) + sizes.localSize (primitive .add₁) +
        512 * allowance + 56 := by
  rw [badHash.eq_def]
  have hr := backendReply_description (indexTy := index.ty) (messageTy := index.messageTy) rep data cost primitive sizes allowance laws dataLaws
    false (Read.badRead rep data cost primitive sampling index) (LazyAGM.badResponse false)
  rw [LazyAGM.badResponse_description] at hr
  have hv := Read.badRead_description rep data cost primitive sizes allowance laws dataLaws sampling index
  simp only [Bool.false_eq_true, ite_false] at hr
  omega

theorem badSign_description :
    (badSign rep data cost primitive sampling index).descriptionSize sizes ≤
      2 * sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .keyEq) +
        2 * sizes.localSize (primitive (.finVal index.bound)) +
        2 * sizes.localSize (primitive .natEq) +
        5 * sizes.localSize (primitive .zero) +
        3 * sizes.localSize (primitive .scale₁) + sizes.localSize (primitive .add₁) +
        2 * sizes.localSize (primitive .add) + 2 * sizes.localSize (primitive .mul) +
        sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) +
        sizes.localSize (primitive (.finZero index.bound)) +
        index.termsDescription allowance (fun instr => sizes.localSize (primitive instr)) +
        1400 * allowance + 176 := by
  rw [badSign.eq_def]
  have hr := backendReply_description (indexTy := index.ty) (messageTy := index.messageTy) rep data cost primitive sizes allowance laws dataLaws
    true (badSignValue rep data cost primitive sampling index) (LazyAGM.badResponse true)
  rw [LazyAGM.badResponse_description] at hr
  have hs := signValue_description rep data cost primitive sizes allowance laws dataLaws
    index.terms index.defaultTerm (Evaluate.backendBad rep data cost primitive sampling index)
  have he := Evaluate.backendBad_description rep data cost primitive sizes allowance laws dataLaws sampling index
  have ht := index.terms_description allowance (fun instr => sizes.localSize (primitive instr))
  have hd := index.default_description allowance (fun instr => sizes.localSize (primitive instr))
  change (badSignValue rep data cost primitive sampling index).descriptionSize sizes ≤ _ at hs
  simp only [ite_true] at hr
  omega

end Reply
end Signatures.Runtime.WeightedAGM
