import Signatures.Runtime.BackendLanguageSize
import Signatures.Runtime.BackendMachine

/-! Stored descriptions for the wrapper machine. Primitive sampler code and
literal values remain visible in the bound. Read/write and entry/exit code are
constructed from generic operations; no complete wrapper-size premise is used. -/

open OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.MachineCompiler

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [SampleableType F]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (samplingCode : SamplingImplementation Q iface rep)
  (sizes : DescriptionSize Q) (allowance : Nat)
  (laws : LocalDescriptionLaws sizes allowance)
  (dataLaws : DataDescriptionLaws sizes rep.data data allowance)

def effectsDescription (store : Ty CryptoAtom) {a b} : Machine.Effect store a b → Nat
  | .scalar => samplingCode.scalar.descriptionSize sizes + 1
  | .uniform n => (samplingCode.uniform n).descriptionSize sizes + 1
  | .read | .write => 3 * allowance + 1

include laws dataLaws

theorem effects_descriptionSize (store : Ty CryptoAtom) {a b} (instr : Machine.Effect store a b) :
    (effects rep data samplingCode store instr).descriptionSize sizes ≤
      effectsDescription rep samplingCode sizes allowance store instr := by
  cases instr with
  | scalar | uniform => rfl
  | read =>
    dsimp only [effects, Code.descriptionSize, effectsDescription]
    apply Nat.add_le_add_right
    exact (laws.pair_bound (laws.snd _ _) (laws.snd _ _)).trans (by omega)
  | write =>
    dsimp only [effects, Code.descriptionSize, effectsDescription]
    apply Nat.add_le_add_right
    exact (laws.pair_bound (dataLaws.unit _) (laws.fst _ _)).trans (by omega)

variable [Field F] [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
  (primitiveBound : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr)

include primitiveBound

theorem program_descriptionSize (store : Ty CryptoAtom) {Γ a}
    (source : Program CryptoOp (Machine.Effect store) Γ a) :
    (program rep data samplingCode cost primitive store source).descriptionSize sizes ≤
      Language.descriptionBound allowance primitiveSize (effectsDescription rep samplingCode sizes allowance store) source := by
  exact Language.compile_descriptionSize sizes allowance laws rep data (arithmetic F G₁ G₂ K M cost) primitive
    dataLaws primitiveSize primitiveBound (rep.ty store) (effects rep data samplingCode store)
    (effectsDescription rep samplingCode sizes allowance store)
    (effects_descriptionSize rep data samplingCode sizes allowance laws dataLaws store) source

theorem unary_descriptionSize (store : Ty CryptoAtom) {a b}
    (source : Program CryptoOp (Machine.Effect store) [a] b) :
    (unary rep data samplingCode cost primitive store source).descriptionSize sizes ≤
      Language.descriptionBound allowance primitiveSize (effectsDescription rep samplingCode sizes allowance store) source +
        5 * allowance + 2 := by
  have hb := program_descriptionSize rep data samplingCode sizes allowance laws dataLaws cost primitive primitiveSize primitiveBound store source
  have hi : sizes.localSize (QP.pair (QP.pair (QP.fst (rep.ty a) (rep.ty store))
      (data.unit (StepClass.HasProd.prod (rep.ty a) (rep.ty store)))) (QP.snd (rep.ty a) (rep.ty store))) ≤ 5 * allowance :=
    (laws.pair_bound (laws.pair_bound (laws.fst _ _) (dataLaws.unit _)) (laws.snd _ _)).trans (by omega)
  dsimp only [unary, Code.descriptionSize]
  omega

theorem closed_descriptionSize {Γ a} (source : Machine.Code Γ a) :
    (closed rep data samplingCode cost primitive source).descriptionSize sizes ≤
      Expression.descriptionBound allowance primitiveSize source.init +
      Language.descriptionBound allowance primitiveSize (effectsDescription rep samplingCode sizes allowance source.store) source.body +
        3 * allowance + 4 := by
  have hb := program_descriptionSize rep data samplingCode sizes allowance laws dataLaws cost primitive primitiveSize primitiveBound
    source.store source.body
  have he := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes allowance laws dataLaws
    primitiveSize primitiveBound source.init
  have hi : sizes.localSize (QP.pair (Q.identity (rep.env Γ))
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive source.init)) ≤
      Expression.descriptionBound allowance primitiveSize source.init + 2 * allowance :=
    (laws.pair_bound (laws.identity _) he).trans (by omega)
  have ho := laws.fst (rep.ty a) (rep.ty source.store)
  dsimp only [closed, Code.descriptionSize]
  omega

end Signatures.Runtime.BackendProgram.MachineCompiler
