import Proofs.Runtime.BackendSchnorrNonzeroSigning
import Proofs.Runtime.BackendExpressionCost
import Proofs.Runtime.BackendSize

/-! The actual nonzero repair expression has a derived local runtime and
output-size bound. All projections, the identity test, selected arithmetic and
retained branch environment are charged from original backend contracts. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.NonzeroSigning.Native

open BackendProgram

def repairTime (overhead : Nat → Nat) (width zeroTime pointTime scaleTime addTime : Nat) : Nat :=
  zeroTime + pointTime + scaleTime + addTime + 128 * overhead (128 * width)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes mono

theorem repair_expression_time (R : G₁) (z a : F) (g : G₁)
    (width zeroTime pointTime scaleTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.env [point₁, scalar, scalar, point₁]) (R, z, a, g, ()) ≤ width)
    (hz : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hs : Q.size (rep.ty point₁) (a • g) ≤ width)
    (ha : Q.size (rep.ty scalar) (z + a) ≤ width)
    (htz : (primitiveBound .zero₁).time () ≤ zeroTime)
    (htp : (primitiveBound .point₁Eq).time (R, 0) ≤ pointTime)
    (hts : (primitiveBound .scale₁).time (a, g) ≤ scaleTime)
    (hta : (primitiveBound .add).time (z, a) ≤ addTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      repair).time (R, z, a, g, ()) ≤ repairTime overhead width zeroTime pointTime scaleTime addTime := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 128 * width, overhead n ≤ overhead (128 * width) := fun _ hn => mono hn
  by_cases h : R = 0 <;>
    dsimp only [repairTime, repair, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.castFunction, LocalBound.elim, DataCostLaws.selectBound, DataCostLaws.unitBound,
      Expr.denote, Var.get, arithmetic, Sum.elim,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at * <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte] at * <;>
    grind only

omit mono [Q.HasCategory] [Q.HasProd] [Q.HasSum] in
theorem repair_output_size (R : G₁) (z a : F) (g : G₁) (width : Nat)
    (hh : header ≤ width)
    (hi : Q.size (rep.env [point₁, scalar, scalar, point₁]) (R, z, a, g, ()) ≤ width)
    (hs : Q.size (rep.ty point₁) (a • g) ≤ width)
    (ha : Q.size (rep.ty scalar) (z + a) ≤ width) :
    Q.size (rep.ty (.pair point₁ scalar))
      (repair.denote (arithmetic F G₁ G₂ K M cost) (R, z, a, g, ())) ≤ 3 * width := by
  rw [repair_denote]
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  by_cases h : R = 0 <;> simp only [h, ↓reduceIte] <;>
    dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env] at * <;>
    grind only

omit sizes mono in
theorem repairTime_polynomial (overhead : Nat → Nat → Nat)
    (width zeroTime pointTime scaleTime addTime : Nat → Nat)
    (hOverhead : PolynomialOverhead overhead) (hWidth : PolynomiallyBounded width)
    (hZero : PolynomiallyBounded zeroTime) (hPoint : PolynomiallyBounded pointTime)
    (hScale : PolynomiallyBounded scaleTime) (hAdd : PolynomiallyBounded addTime) :
    PolynomiallyBounded (fun n => repairTime (overhead n) (width n) (zeroTime n) (pointTime n) (scaleTime n) (addTime n)) :=
  (((hZero.add hPoint).add hScale).add hAdd).add
    ((PolynomiallyBounded.const 128).mul (hOverhead.apply ((PolynomiallyBounded.const 128).mul hWidth)))

end Signatures.Runtime.Schnorr.NonzeroSigning.Native
