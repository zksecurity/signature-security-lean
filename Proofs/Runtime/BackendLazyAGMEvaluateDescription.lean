import Proofs.Runtime.BackendLazyAGMEvaluate
import Proofs.Runtime.BackendLazyAGMReadDescription
import Proofs.Runtime.BackendWeakeningSize

/-! Stored descriptions of the complete native row evaluators. Each loop
stores one body; list lengths and counters are runtime data. Private-read code,
its sampler, all arithmetic instructions, and structural adapters are charged. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
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

theorem backendEvaluate_description {value : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value)
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    (backendEvaluate rep data cost primitive sampler fallback zero combine).descriptionSize sizes ≤
      sampler.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) fallback +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) zero +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) combine +
        sizes.localSize (primitive .natEq) + sizes.localSize (primitive .natSub) +
        2 * sizes.localSize (primitive .natAdd) + 1024 * allowance + 128 := by
  have hr := backendRead_description rep data cost primitive sizes allowance laws dataLaws sampler fallback
  rw [backendEvaluate]
  have h := Language.compile_descriptionSize sizes allowance laws rep data
    (arithmetic F G₁ G₂ M M cost) primitive dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (rep.ty (cacheTy value)) (readEffect rep data cost primitive sampler fallback)
    (fun _ => sampler.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
      Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) fallback +
      288 * allowance + 36)
    (fun instr => by cases instr; exact hr) (evaluateRows zero combine)
  refine h.trans ?_
  simp only [evaluateRows, evalBody, selectRow, evalUpdate, listLength,
    Language.descriptionBound, Expression.descriptionBound,
    Expression.descriptionBound_weakenTail, index, indexBody,
    v0, v1, v2, v3, Expression.variableDescription]
  omega

variable [SampleableType F]

theorem backendEvaluateGood_description (sampling : MachineCompiler.SamplingImplementation Q iface rep) :
    (backendEvaluateGood rep data cost primitive sampling).descriptionSize sizes ≤
      sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        2 * sizes.localSize (primitive .zero) + sizes.localSize (primitive .add) +
        sizes.localSize (primitive .mul) + sizes.localSize (primitive .natEq) +
        sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) +
        1100 * allowance + 128 := by
  rw [backendEvaluateGood]
  have h := backendEvaluate_description rep data cost primitive sizes allowance laws dataLaws
    sampling.scalar (.op .zero .unit) (.op .zero .unit) goodCombine
  simp only [goodCombine, v0, v1, v2, Expression.descriptionBound,
    Expression.variableDescription] at h ⊢
  omega

theorem backendEvaluateBad_description (sampling : MachineCompiler.SamplingImplementation Q iface rep) :
    (backendEvaluateBad rep data cost primitive sampling).descriptionSize sizes ≤
      2 * sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .messageEq) +
        4 * sizes.localSize (primitive .zero) + 2 * sizes.localSize (primitive .add) +
        2 * sizes.localSize (primitive .mul) + sizes.localSize (primitive .natEq) +
        sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) +
        1200 * allowance + 144 := by
  rw [backendEvaluateBad]
  have h := backendEvaluate_description rep data cost primitive sizes allowance laws dataLaws
    (pairSampler rep data sampling) (.pair (.op .zero .unit) (.op .zero .unit))
    (.pair (.op .zero .unit) (.op .zero .unit)) badCombine
  have hs := PairSampling.description rep.data data (rep.ty scalar) (rep.ty scalar)
    sampling.scalar sampling.scalar sizes allowance laws dataLaws
  change (pairSampler rep data sampling).descriptionSize sizes ≤ _ at hs
  simp only [badCombine, v0, v1, v2, Expression.descriptionBound,
    Expression.variableDescription] at h ⊢
  omega

end Signatures.Runtime.LazyAGM
