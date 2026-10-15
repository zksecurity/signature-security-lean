import Signatures.Runtime.BackendSchnorrAGMComparison
import Signatures.Runtime.BackendSampledCache

/-! A fresh Schnorr cache entry is constructed after a scalar draw while retaining
the affine explanation fixed before that draw. The exceptional-challenge flag
is updated by explicit field addition and equality code. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native

open BackendProgram

abbrev readStoreTy : Ty CryptoAtom := .pair affineTy .bool
abbrev ReadStore (F : Type) := (F × F) × Bool

def freshValue {F : Type} [Field F] [DecidableEq F] (input : F × ReadStore F) :
    EncodedEntry F × ReadStore F :=
  ((input.1, true, input.2.1), input.2.1, input.2.2 || decide (input.2.1.2 + input.1 = 0))

def freshExpression : Expr CryptoOp [.pair scalar readStoreTy] (.pair entryTy readStoreTy) :=
  .pair
    (.pair (.fst (.var .here)) (.pair (.bool true) (.fst (.snd (.var .here)))))
    (.pair (.fst (.snd (.var .here)))
      (.branch (.snd (.snd (.var .here))) (.bool true)
        (.op .scalarEq (.pair
          (.op .add (.pair (.snd (.fst (.snd (.var .here)))) (.fst (.var .here))))
          (.op .zero .unit)))))

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem freshExpression_value (cost : PrimitiveCosts) (input : F × ReadStore F) :
    freshExpression.denote (arithmetic F G₁ G₂ K M cost) (input, ()) = freshValue input := by
  cases hb : input.2.2 <;> simp [freshExpression, Expr.denote, Var.get, arithmetic, freshValue, hb]
  rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def freshFrame : Q.Realizer (rep.ty (.pair scalar readStoreTy))
    (rep.env [.pair scalar readStoreTy]) (fun input => (input, ())) :=
  QP.pair (Q.identity _) (data.unit _)

def freshCode : Q.Realizer (rep.ty (.pair scalar readStoreTy))
    (rep.ty (.pair entryTy readStoreTy)) freshValue :=
  (Q.compose (freshFrame rep data)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive freshExpression)).castFunction
      (by funext input; exact freshExpression_value cost input)

variable {iface : Interface (C := C) unifSpec}
  (sampler : Code Q unifSpec iface rep.data.unit (rep.ty scalar))

/-- The retained explanation is ordinary represented runtime input, not a
constant captured by the sampler's code. -/
def freshSample : Code Q unifSpec iface (rep.ty (.pair .unit readStoreTy))
    (rep.ty (.pair entryTy readStoreTy)) :=
  .seq (.first (rep.ty readStoreTy) sampler) (.atomic (freshCode rep data cost primitive))

theorem freshSample_denote (saved : ReadStore F) :
    (freshSample rep data cost primitive sampler).denote ((), saved) =
      (fun c => freshValue (c, saved)) <$> sampler.denote () := by
  simp only [freshSample, Code.denote, bind_pure_comp, Functor.map_map]

theorem freshCode_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    sizes.localSize (freshCode rep data cost primitive) ≤
      primitiveSize .add + primitiveSize .zero + primitiveSize .scalarEq + 128 * allowance := by
  rw [freshCode, DescriptionSize.castFunction]
  have he := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes
    allowance laws dataLaws primitiveSize hp freshExpression
  have hf := laws.pair_bound (laws.identity (rep.ty (.pair scalar readStoreTy)))
    (dataLaws.unit (rep.ty (.pair scalar readStoreTy)))
  have hc := laws.compose_bound hf he
  simp only [freshExpression, Expression.descriptionBound, Expression.variableDescription] at hc
  exact hc.trans (by omega)

theorem freshSample_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    (freshSample rep data cost primitive sampler).descriptionSize sizes ≤
      sampler.descriptionSize sizes + primitiveSize .add + primitiveSize .zero +
        primitiveSize .scalarEq + 128 * allowance + 3 := by
  have h := freshCode_description rep data cost primitive sizes allowance laws dataLaws primitiveSize hp
  dsimp only [freshSample, Code.descriptionSize]
  omega

end Signatures.Runtime.SchnorrAGM.Native
