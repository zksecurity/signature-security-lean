import Proofs.Runtime.BackendSchnorrAGMExtraction
import Proofs.Runtime.BackendCallerDescription

/-! Stored-code bounds for the full native Schnorr terminal. They count the
sampler, every primitive, scans, adapters and branch bodies independently of
runtime list lengths, message universes and random arities. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native

open BackendProgram

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
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
  (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
  (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr)

include laws dataLaws hp

theorem EntryRead.description :
    (EntryRead.code rep data cost primitive sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + primitiveSize .messageEq + primitiveSize .point₁Eq +
        primitiveSize .add + 2 * primitiveSize .zero + primitiveSize .scalarEq + 1100 * allowance + 48 := by
  have hframe (ty : Ty CryptoAtom) : sizes.localSize (Read.frame rep data ty) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have hsetup : sizes.localSize (Read.setup rep data cost primitive) ≤ primitiveSize .zero + 256 * allowance := by
    rw [Read.setup, DescriptionSize.castFunction]
    have h := laws.compose_bound (hframe Read.inputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
        primitiveSize hp Read.setupExpression)
    refine h.trans ?_
    simp only [Read.setupExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hfinish : sizes.localSize (EntryRead.finish rep data cost primitive) ≤ 256 * allowance := by
    unfold EntryRead.finish
    have h := laws.compose_bound (hframe Read.retainedOutputTy)
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
        primitiveSize hp EntryRead.returnExpression)
    refine h.trans ?_
    simp only [EntryRead.returnExpression, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hc := cacheAccess_description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  dsimp only [EntryRead.code, Code.descriptionSize]
  omega

theorem Extraction.localCode_description {a b : Ty CryptoAtom} (expression : Expr CryptoOp [a] b) :
    sizes.localSize (Extraction.localCode rep data cost primitive expression) ≤
      Expression.descriptionBound allowance primitiveSize expression + 4 * allowance := by
  have hframe : sizes.localSize (Read.frame rep data a) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  exact (laws.compose_bound hframe
    (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
      primitiveSize hp expression)).trans (by omega)

theorem Extraction.decoded_description :
    (Extraction.decoded rep data cost primitive sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + primitiveSize .messageEq + primitiveSize .point₁Eq +
        4 * primitiveSize .add + 4 * primitiveSize .zero + primitiveSize .scalarEq +
        primitiveSize .natEq + primitiveSize .natSub + primitiveSize .natAdd +
        2 * primitiveSize .mul + primitiveSize .sub + primitiveSize .div + 5000 * allowance + 128 := by
  have hh := Hash.prepare_description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
  have hr := EntryRead.description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  have hf := Extraction.localCode_description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
    Extraction.finishExpression
  have hf' : sizes.localSize (Extraction.localCode rep data cost primitive Extraction.finishExpression) ≤
      primitiveSize .sub + primitiveSize .add + primitiveSize .div + primitiveSize .zero + 128 * allowance :=
    hf.trans (by simp only [Extraction.finishExpression, Expression.descriptionBound, Expression.variableDescription]; omega)
  dsimp only [Extraction.decoded, Extraction.prepared, Code.descriptionSize]
  omega

variable [C.HasOption] [Q.HasOption] [OptionCode (Q := Q)]
  [QD : Q.IsDistributive] (dispatch : DispatchDescriptionLaws (Q := Q) sizes allowance)

include dispatch

theorem Extraction.description :
    (Extraction.code rep data cost primitive sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + primitiveSize .messageEq + primitiveSize .point₁Eq +
        4 * primitiveSize .add + 5 * primitiveSize .zero + primitiveSize .zero₁ + primitiveSize .scalarEq +
        primitiveSize .natEq + primitiveSize .natSub + primitiveSize .natAdd +
        2 * primitiveSize .mul + primitiveSize .sub + primitiveSize .div + 7000 * allowance + 160 := by
  have hframe : sizes.localSize (Read.frame rep data HashDispatch.inputTy) ≤ 3 * allowance :=
    (laws.pair_bound (laws.identity _) (dataLaws.unit _)).trans (by omega)
  have hprepare : sizes.localSize (HashDispatch.prepare rep data cost primitive) ≤ primitiveSize .zero₁ + 1000 * allowance := by
    rw [HashDispatch.prepare, DescriptionSize.castFunction]
    have h := laws.compose_bound hframe
      (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
        primitiveSize hp HashDispatch.prepareExpression)
    refine h.trans ?_
    simp only [HashDispatch.prepareExpression, HashDispatch.prepareWith, HashDispatch.groupWith,
      HashDispatch.rowWith, ListSingleton.scan, ListSingleton.body,
      Expression.descriptionBound, Expression.variableDescription]
    omega
  have hroute : sizes.localSize (HashDispatch.route rep data cost primitive) ≤ primitiveSize .zero₁ + 1002 * allowance :=
    (laws.compose_bound hprepare (dataLaws.select (rep.ty Hash.inputTy))).trans (by omega)
  have hstart := Extraction.localCode_description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
    Extraction.startExpression
  have hreject := Extraction.localCode_description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
    Extraction.rejectExpression
  have hstart' : sizes.localSize (Extraction.localCode rep data cost primitive Extraction.startExpression) ≤ 256 * allowance :=
    hstart.trans (by simp only [Extraction.startExpression, Expression.descriptionBound, Expression.variableDescription]; omega)
  have hreject' : sizes.localSize (Extraction.localCode rep data cost primitive Extraction.rejectExpression) ≤
      primitiveSize .zero + 256 * allowance :=
    hreject.trans (by simp only [Extraction.rejectExpression, Expression.descriptionBound, Expression.variableDescription]; omega)
  have hdecoded := Extraction.decoded_description rep data cost primitive sampler sizes allowance laws dataLaws primitiveSize hp
  have hd := dispatch.distribute (rep.ty Hash.inputTy) (rep.ty Hash.inputTy) (rep.ty scalar)
  dsimp only [Extraction.code, Extraction.branches, Code.descriptionSize]
  omega

end Signatures.Runtime.SchnorrAGM.Native
