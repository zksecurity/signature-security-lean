import Signatures.Runtime.KeyEquality
import Signatures.Runtime.BackendExpressionCost
import Signatures.Runtime.BackendExpressionSize
import Signatures.Runtime.BackendDataSize

/-! Native costs of comparing weighted-cache indices. Both the topic/slot and
the degree/coordinate tag are compared by implemented syntax. The topic/slot
domain is arbitrary; its comparison is charged at the supplied encoding widths.
-/

open PFunctor

namespace Signatures.Runtime.AGM.KeyEquality

open BackendProgram

theorem oops_description (d allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) :
    Expression.descriptionBound allowance primitiveSize (oops d) ≤
      primitiveSize .keyEq + 2 * primitiveSize (.finVal d) + primitiveSize .natEq + 64 * allowance := by
  simp only [oops, Expression.descriptionBound, Expression.variableDescription]
  omega

theorem proximity_description (ell allowance : Nat)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat) :
    Expression.descriptionBound allowance primitiveSize (proximity ell) ≤
      primitiveSize .keyEq + 2 * primitiveSize (.finVal ell) + primitiveSize .natEq + 64 * allowance := by
  simp only [proximity, Expression.descriptionBound, Expression.variableDescription]
  omega

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

omit [C.HasOption] in
theorem oops_code_size (d : Nat) (descriptions : DescriptionSize Q) (allowance : Nat)
    (descriptionLaws : LocalDescriptionLaws descriptions allowance)
    (descriptionData : DataDescriptionLaws descriptions rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), descriptions.localSize (primitive instr) ≤ primitiveSize instr) :
    descriptions.localSize (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (oops d)) ≤
      primitiveSize .keyEq + 2 * primitiveSize (.finVal d) + primitiveSize .natEq + 64 * allowance :=
  (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive descriptions allowance
    descriptionLaws descriptionData primitiveSize hp (oops d)).trans (oops_description d allowance primitiveSize)

omit [C.HasOption] in
theorem proximity_code_size (ell : Nat) (descriptions : DescriptionSize Q) (allowance : Nat)
    (descriptionLaws : LocalDescriptionLaws descriptions allowance)
    (descriptionData : DataDescriptionLaws descriptions rep.data data allowance)
    (primitiveSize : {a b : Ty CryptoAtom} → CryptoOp a b → Nat)
    (hp : ∀ {a b} (instr : CryptoOp a b), descriptions.localSize (primitive instr) ≤ primitiveSize instr) :
    descriptions.localSize (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (proximity ell)) ≤
      primitiveSize .keyEq + 2 * primitiveSize (.finVal ell) + primitiveSize .natEq + 64 * allowance :=
  (Expression.compile_size rep data (arithmetic F G₁ G₂ K M cost) primitive descriptions allowance
    descriptionLaws descriptionData primitiveSize hp (proximity ell)).trans
      (proximity_description ell allowance primitiveSize)

include laws dataLaws sizes mono

theorem oops_cost (d : Nat) (x y : K × Fin (d + 1)) (width topicTime indexTime natTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ d, Q.size rep.data.nat j ≤ width)
    (hx : Q.size (rep.ty (Weights.oopsKey d)) x ≤ width)
    (hy : Q.size (rep.ty (Weights.oopsKey d)) y ≤ width)
    (ht : ∀ a b : K, Q.size (rep.ty key) a ≤ width → Q.size (rep.ty key) b ≤ width →
      (primitiveBound .keyEq).time (a, b) ≤ topicTime)
    (hi : ∀ j : Fin (d + 1), (primitiveBound (.finVal d)).time j ≤ indexTime)
    (he : ∀ j k : Nat, j ≤ d → k ≤ d → (primitiveBound .natEq).time (j, k) ≤ natTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (oops d)) (x, y, ()) ≤
      topicTime + 2 * indexTime + natTime + 128 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound (oops d) (x, y, ())).trans ?_
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hkx := (sizes.fst_le (rep.ty key) (rep.ty (boundedNat d)) x).trans hx
  have hky := (sizes.fst_le (rep.ty key) (rep.ty (boundedNat d)) y).trans hy
  have htt := ht x.1 y.1 hkx hky
  have hix := hi x.2
  have hiy := hi y.2
  have hnx := hn x.2.val (by omega)
  have hny := hn y.2.val (by omega)
  have hee := he x.2.val y.2.val (by omega) (by omega)
  have hleft := sizes.sum_le (rep.env [Weights.oopsKey d, Weights.oopsKey d])
    (rep.env [Weights.oopsKey d, Weights.oopsKey d]) (.inl (x, y, ()))
  have hright := sizes.sum_le (rep.env [Weights.oopsKey d, Weights.oopsKey d])
    (rep.env [Weights.oopsKey d, Weights.oopsKey d]) (.inr (x, y, ()))
  dsimp only [Sum.elim] at hleft hright
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ h => mono h
  by_cases htopic : x.1 = y.1 <;>
    dsimp only [oops, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.castFunction, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.boolBound,
      DataCostLaws.selectBound, Expr.denote, Var.get, arithmetic,
      id, Function.comp_def, Sum.elim] <;>
    simp only [htopic, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;>
    dsimp only [arithmetic,
      LanguageRepresentation.ty, LanguageRepresentation.env] at * <;>
    clear ht hi he hn <;>
    grind only

theorem proximity_cost (ell : Nat) (x y : Fin (ell + 1) × K) (width slotTime indexTime natTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn : ∀ j ≤ ell, Q.size rep.data.nat j ≤ width)
    (hx : Q.size (rep.ty (Weights.proximityKey ell)) x ≤ width)
    (hy : Q.size (rep.ty (Weights.proximityKey ell)) y ≤ width)
    (ht : ∀ a b : K, Q.size (rep.ty key) a ≤ width → Q.size (rep.ty key) b ≤ width →
      (primitiveBound .keyEq).time (a, b) ≤ slotTime)
    (hi : ∀ j : Fin (ell + 1), (primitiveBound (.finVal ell)).time j ≤ indexTime)
    (he : ∀ j k : Nat, j ≤ ell → k ≤ ell → (primitiveBound .natEq).time (j, k) ≤ natTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (proximity ell)) (x, y, ()) ≤
      slotTime + 2 * indexTime + natTime + 128 * overhead (128 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound (proximity ell) (x, y, ())).trans ?_
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hkx := (sizes.snd_le (rep.ty (boundedNat ell)) (rep.ty key) x).trans hx
  have hky := (sizes.snd_le (rep.ty (boundedNat ell)) (rep.ty key) y).trans hy
  have htt := ht x.2 y.2 hkx hky
  have hix := hi x.1
  have hiy := hi y.1
  have hnx := hn x.1.val (by omega)
  have hny := hn y.1.val (by omega)
  have hee := he x.1.val y.1.val (by omega) (by omega)
  have hleft := sizes.sum_le (rep.env [Weights.proximityKey ell, Weights.proximityKey ell])
    (rep.env [Weights.proximityKey ell, Weights.proximityKey ell]) (.inl (x, y, ()))
  have hright := sizes.sum_le (rep.env [Weights.proximityKey ell, Weights.proximityKey ell])
    (rep.env [Weights.proximityKey ell, Weights.proximityKey ell]) (.inr (x, y, ()))
  dsimp only [Sum.elim] at hleft hright
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ h => mono h
  by_cases hslot : x.2 = y.2 <;>
    dsimp only [proximity, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.castFunction, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.boolBound,
      DataCostLaws.selectBound, Expr.denote, Var.get, arithmetic,
      id, Function.comp_def, Sum.elim] <;>
    simp only [hslot, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false] <;>
    dsimp only [arithmetic,
      LanguageRepresentation.ty, LanguageRepresentation.env] at * <;>
    clear ht hi he hn <;>
    grind only

end Signatures.Runtime.AGM.KeyEquality
