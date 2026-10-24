import Proofs.Runtime.SchnorrAGMEncoding
import Proofs.Runtime.BackendComparison

/-! Native comparison of message/commitment cache keys. Both component tests
are implemented in the declared backend; their encoding-dependent costs and
the comparison routine's stored description are charged. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native

open BackendProgram

def keyEquality : Expr CryptoOp [cacheKeyTy, cacheKeyTy] .bool :=
  .branch (.op .messageEq (.pair (.fst (.var .here)) (.fst (.var (.there .here)))))
    (.op .point₁Eq (.pair (.snd (.var .here)) (.snd (.var (.there .here))))) (.bool false)

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem keyEquality_value (cost : PrimitiveCosts) (x y : M × G₁) :
    keyEquality.denote (arithmetic F G₁ G₂ K M cost) (x, y, ()) = decide (x = y) := by
  by_cases h : x.1 = y.1 <;>
    simp [keyEquality, Expr.denote, Var.get, arithmetic, h, Prod.ext_iff]
  rfl

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))

def comparison : Q.Realizer (rep.ty (.pair cacheKeyTy cacheKeyTy)) rep.data.bool
    (fun p => decide (p.1 = p.2)) :=
  Comparison.code rep data (arithmetic F G₁ G₂ K M cost) primitive keyEquality (keyEquality_value cost)

theorem comparison_description (sizes : DescriptionSize Q) (allowance : Nat)
    (laws : LocalDescriptionLaws sizes allowance)
    (dataLaws : DataDescriptionLaws sizes rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), sizes.localSize (primitive instr) ≤ primitiveSize instr) :
    sizes.localSize (comparison rep data cost primitive) ≤
      primitiveSize .messageEq + primitiveSize .point₁Eq + 64 * allowance := by
  have he := Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive sizes
    allowance laws dataLaws primitiveSize hp keyEquality
  have hc := Comparison.description rep data (arithmetic F G₁ G₂ K M cost) primitive
    keyEquality (keyEquality_value cost) sizes allowance laws dataLaws
  have hs : Expression.descriptionBound allowance primitiveSize keyEquality ≤
      primitiveSize .messageEq + primitiveSize .point₁Eq + 58 * allowance := by
    simp only [keyEquality, Expression.descriptionBound, Expression.variableDescription]
    omega
  have hb := he.trans hs
  exact hc.trans (by omega)

variable [C.HasOption]
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes laws dataLaws mono

theorem keyEquality_cost (x y : M × G₁) (width messageTime pointTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hx : Q.size (rep.ty cacheKeyTy) x ≤ width) (hy : Q.size (rep.ty cacheKeyTy) y ≤ width)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ width → Q.size (rep.ty message) b ≤ width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ width → Q.size (rep.ty point₁) b ≤ width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive keyEquality) (x, y, ()) ≤
      messageTime + pointTime + 128 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound keyEquality (x, y, ())).trans ?_
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hmessage := hm x.1 y.1 ((sizes.fst_le _ _ x).trans hx) ((sizes.fst_le _ _ y).trans hy)
  have hpoint := hg x.2 y.2 ((sizes.snd_le _ _ x).trans hx) ((sizes.snd_le _ _ y).trans hy)
  have hleft := sizes.sum_le (rep.env [cacheKeyTy, cacheKeyTy]) (rep.env [cacheKeyTy, cacheKeyTy])
    (.inl (x, y, ()))
  have hright := sizes.sum_le (rep.env [cacheKeyTy, cacheKeyTy]) (rep.env [cacheKeyTy, cacheKeyTy])
    (.inr (x, y, ()))
  dsimp only [Sum.elim] at hleft hright
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ h => mono h
  by_cases h : x.1 = y.1 <;>
    dsimp only [keyEquality, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.castFunction, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.boolBound,
      DataCostLaws.selectBound, Expr.denote, Var.get, arithmetic,
      id, Function.comp_def, Sum.elim] <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;>
    dsimp only [arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env] at * <;>
    clear hm hg <;> grind only

theorem comparison_cost (x y : M × G₁) (width messageTime pointTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hx : Q.size (rep.ty cacheKeyTy) x ≤ width) (hy : Q.size (rep.ty cacheKeyTy) y ≤ width)
    (hm : ∀ a b : M, Q.size (rep.ty message) a ≤ width → Q.size (rep.ty message) b ≤ width →
      (primitiveBound .messageEq).time (a, b) ≤ messageTime)
    (hg : ∀ a b : G₁, Q.size (rep.ty point₁) a ≤ width → Q.size (rep.ty point₁) b ≤ width →
      (primitiveBound .point₁Eq).time (a, b) ≤ pointTime) :
    Q.cost (comparison rep data cost primitive) (x, y) ≤
      messageTime + pointTime + 134 * overhead (128 * width) := by
  have hc := keyEquality_cost rep data cost primitive sizes laws dataLaws primitiveBound mono
    x y width messageTime pointTime hh hu hb hx hy hm hg
  have ha := Comparison.cost rep data (arithmetic F G₁ G₂ K M cost) primitive sizes laws dataLaws mono
    keyEquality (keyEquality_value cost) x y width
    (messageTime + pointTime + 128 * overhead (128 * width)) hh hu hb hx hy hc
  have hs : overhead (16 * width) ≤ overhead (128 * width) := mono (by omega)
  exact ha.trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native
