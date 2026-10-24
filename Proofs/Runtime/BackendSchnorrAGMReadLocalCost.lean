import Proofs.Runtime.BackendSchnorrAGMReadSize

/-! Actual local setup/return costs for a native Schnorr read. The compiled
expressions construct the default entry and route every retained component;
there is no supplied cost premise for either completed adapter. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Read

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

include sizes laws dataLaws mono

theorem framed_cost {input output : Ty CryptoAtom} (e : Expr CryptoOp [input] output)
    (x : input.Value (cryptoBase F G₁ G₂ K M)) (width time : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty input) x ≤ width)
    (ho : Q.size (rep.ty output) (e.denote (arithmetic F G₁ G₂ K M cost) (x, ())) ≤ 32 * width)
    (he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive e) (x, ()) ≤ time) :
    Q.cost (Q.compose (frame rep data input)
      (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive e)) x ≤
        time + 4 * overhead (256 * width) := by
  have hf := (LocalBound.pair laws (LocalBound.identity laws (rep.ty input))
    (dataLaws.unitBound (rep.ty input))).cost_le x
  have hc := laws.compose (frame rep data input)
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive e) x
  have henv : Q.size (rep.env [input]) (x, ()) ≤ 3 * width := by
    have hp := sizes.prod_le (rep.ty input) rep.data.unit (x, ())
    dsimp only at hp
    exact hp.trans (by omega)
  have hfee : ∀ k ≤ 256 * width, overhead k ≤ overhead (256 * width) := fun _ h => mono h
  dsimp only [LocalBound.pair, LocalBound.identity, DataCostLaws.unitBound, id] at hf
  have hframe : Q.cost (frame rep data input) x ≤ 3 * overhead (256 * width) :=
    hf.trans (by
      have h₁ := hfee _ (show Q.size (rep.ty input) x ≤ 256 * width by omega)
      have h₂ := hfee _ (show Q.size (rep.ty input) x + Q.size rep.data.unit () ≤ 256 * width by omega)
      have h₃ := hfee _ (show Q.size (rep.ty input) x + Q.size (rep.env [input]) (x, ()) ≤ 256 * width by omega)
      dsimp only [LanguageRepresentation.env] at h₃
      omega)
  have hj := hfee _ (show Q.size (rep.ty input) x + Q.size (rep.env [input]) (x, ()) +
    Q.size (rep.ty output) (e.denote (arithmetic F G₁ G₂ K M cost) (x, ())) ≤ 256 * width by omega)
  exact hc.trans (by omega)

theorem setup_cost (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (width fieldTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.ty inputTy) input ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime) :
    Q.cost (setup rep data cost primitive) input ≤ fieldTime + 516 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty retainedInputTy) (packValue input) ≤ 32 * width := by
    dsimp only [packValue, setupValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive setupExpression)
      (input, ()) ≤ fieldTime + 512 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound setupExpression (input, ())).trans ?_
    have hfee : ∀ k ≤ 256 * width, overhead k ≤ overhead (256 * width) := fun _ h => mono h
    dsimp only [setupExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.boolBound, Expr.denote, Var.get, arithmetic,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  rw [setup, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := framed_cost rep data cost primitive sizes laws dataLaws mono setupExpression input width
    (fieldTime + 512 * overhead (256 * width)) hh hu hi hout he
  exact h.trans (by omega)

include primitiveBound in
theorem finish_cost (input : retainedOutputTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty retainedOutputTy) input ≤ width) :
    Q.cost (finish rep data cost primitive) input ≤ 260 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty outputTy) (returnValue input) ≤ 32 * width := by
    dsimp only [returnValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive returnExpression)
      (input, ()) ≤ 256 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound returnExpression (input, ())).trans ?_
    have hfee : ∀ k ≤ 256 * width, overhead k ≤ overhead (256 * width) := fun _ h => mono h
    dsimp only [returnExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      Expr.denote, Var.get, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  rw [finish, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := framed_cost rep data cost primitive sizes laws dataLaws mono returnExpression input width
    (256 * overhead (256 * width)) hh hu hi hout he
  exact h.trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native.Read
