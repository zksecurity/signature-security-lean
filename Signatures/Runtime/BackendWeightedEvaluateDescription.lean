import Signatures.Runtime.BackendWeightedEvaluate
import Signatures.Runtime.BackendWeightedReadDescription
import Signatures.Runtime.BackendWeakeningSize

/-! Stored descriptions of the complete native weighted evaluators. Each loop
stores its body once, including the actual read/comparison/sampler code. Term
counts, counters and cache entries are runtime data, not unrolled code. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Evaluate

open BackendProgram Read LazyAGM.ReplySyntax

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

theorem backendEvaluate_description {indexTy value : Ty CryptoAtom}
    (reader : Code Q unifSpec iface (rep.ty (inputTy indexTy value))
      (rep.ty (.pair value (cacheTy indexTy value))))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    (backendEvaluate rep data cost primitive reader zero combine).descriptionSize sizes ≤
      reader.descriptionSize sizes +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) zero +
        Expression.descriptionBound allowance (fun instr => sizes.localSize (primitive instr)) combine +
        sizes.localSize (primitive .natEq) + sizes.localSize (primitive .natSub) +
        2 * sizes.localSize (primitive .natAdd) + 736 * allowance + 92 := by
  rw [backendEvaluate]
  have h := Language.compile_descriptionSize sizes allowance laws rep data
    (arithmetic F G₁ G₂ K M cost) primitive dataLaws
    (fun instr => sizes.localSize (primitive instr)) (fun _ => le_rfl)
    (rep.ty (cacheTy indexTy value)) (readEffect rep reader)
    (fun _ => reader.descriptionSize sizes) (fun instr => by cases instr; rfl)
    (evaluateRows zero combine)
  refine h.trans ?_
  simp only [evaluateRows, evalBody, selectRow, evalUpdate, listLength,
    Language.descriptionBound, Expression.descriptionBound, Expression.descriptionBound_weakenTail,
    index, indexBody, v0, v1, v2, v3, Expression.variableDescription]
  omega

variable [SampleableType F] (sampling : MachineCompiler.SamplingImplementation Q iface rep) (index : Index)

theorem backendGood_description :
    (backendGood rep data cost primitive sampling index).descriptionSize sizes ≤
      sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .keyEq) +
        2 * sizes.localSize (primitive (.finVal index.bound)) + 2 * sizes.localSize (primitive .natEq) +
        2 * sizes.localSize (primitive .zero) + sizes.localSize (primitive .add) + sizes.localSize (primitive .mul) +
        sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) + 1100 * allowance + 128 := by
  have h := backendEvaluate_description rep data cost primitive sizes allowance laws dataLaws
    (goodRead rep data cost primitive sampling index) (.op .zero .unit) goodCombine
  have hr := goodRead_description rep data cost primitive sizes allowance laws dataLaws sampling index
  simp only [goodCombine, v0, v1, v2, Expression.descriptionBound, Expression.variableDescription] at h
  exact h.trans (by omega)

theorem backendBad_description :
    (backendBad rep data cost primitive sampling index).descriptionSize sizes ≤
      2 * sampling.scalar.descriptionSize sizes + sizes.localSize (primitive .keyEq) +
        2 * sizes.localSize (primitive (.finVal index.bound)) + 2 * sizes.localSize (primitive .natEq) +
        4 * sizes.localSize (primitive .zero) + 2 * sizes.localSize (primitive .add) + 2 * sizes.localSize (primitive .mul) +
        sizes.localSize (primitive .natSub) + 2 * sizes.localSize (primitive .natAdd) + 1200 * allowance + 144 := by
  have h := backendEvaluate_description rep data cost primitive sizes allowance laws dataLaws
    (badRead rep data cost primitive sampling index) (.pair (.op .zero .unit) (.op .zero .unit)) badCombine
  have hr := badRead_description rep data cost primitive sizes allowance laws dataLaws sampling index
  simp only [badCombine, v0, v1, v2, Expression.descriptionBound, Expression.variableDescription] at h
  exact h.trans (by omega)

end Signatures.Runtime.WeightedAGM.Evaluate
