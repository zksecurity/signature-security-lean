import Signatures.Runtime.BackendSchnorrAGMExtraction

/-! Derive actual compiled terminal-adapter costs from field and representation
contracts. The zero fallback, subtraction, addition, division and retained
state all have explicit charges; no extractor budget is supplied. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Extraction

open BackendProgram

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
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes laws dataLaws primitiveBound mono

theorem start_cost (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty inputTy) input ≤ width) :
    Q.cost (localCode rep data cost primitive startExpression) input ≤ 260 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty startingTy) (startValue input) ≤ 32 * width := by
    dsimp only [startValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive startExpression)
      (input, ()) ≤ 256 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound startExpression (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [startExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      Expr.denote, Var.get, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono startExpression input width
    (256 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

theorem reject_cost (input : decodedTy.Value (cryptoBase F G₁ G₂ K M)) (width fieldTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.ty decodedTy) input ≤ width) (hz : (primitiveBound .zero).time () ≤ fieldTime) :
    Q.cost (localCode rep data cost primitive rejectExpression) input ≤ fieldTime + 260 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty Read.outputTy) ((0 : F), input.1.2.2) ≤ 32 * width := by
    dsimp only [LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive rejectExpression)
      (input, ()) ≤ fieldTime + 256 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound rejectExpression (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [rejectExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, Expr.denote, Var.get, arithmetic, id, Function.comp_def,
      LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono rejectExpression input width
    (fieldTime + 256 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

theorem finish_cost (input : terminalTy.Value (cryptoBase F G₁ G₂ K M)) (width fieldTime divisionTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hi : Q.size (rep.ty terminalTy) input ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hsub : ∀ a b : F, (primitiveBound .sub).time (a, b) ≤ fieldTime)
    (hadd : ∀ a b : F, (primitiveBound .add).time (a, b) ≤ fieldTime)
    (hdiv : ∀ a b : F, (primitiveBound .div).time (a, b) ≤ divisionTime) :
    Q.cost (localCode rep data cost primitive finishExpression) input ≤
      3 * fieldTime + divisionTime + 1028 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hsum := @sizes.sum_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty Read.outputTy) (finishValue input) ≤ 32 * width := by
    dsimp only [finishValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive finishExpression)
      (input, ()) ≤ 3 * fieldTime + divisionTime + 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound finishExpression (input, ())).trans ?_
    have hleft := sizes.sum_le (rep.env [terminalTy]) (rep.env [terminalTy]) (.inl (input, ()))
    have hright := sizes.sum_le (rep.env [terminalTy]) (rep.env [terminalTy]) (.inr (input, ()))
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    have hsub' := hsub input.2 input.1.1.2.2.1
    have hadd' := hadd input.1.1.2.2.2 input.1.1.1
    have hdiv' := hdiv (input.2 - input.1.1.2.2.1) (input.1.1.2.2.2 + input.1.1.1)
    cases hflag : input.1.1.2.1 <;>
      dsimp only [finishExpression, Expression.compileBound, Expression.variableBound,
        LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
        LocalBound.castFunction, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.selectBound,
        Expr.denote, Var.get, arithmetic, id, Function.comp_def, LanguageRepresentation.ty,
        LanguageRepresentation.env] at * <;>
      simp only [hflag, Bool.false_eq_true, ↓reduceIte, Sum.elim] at * <;>
      clear hsub hadd hdiv <;> grind only
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono finishExpression input width
    (3 * fieldTime + divisionTime + 1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native.Extraction
