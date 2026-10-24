import Proofs.Runtime.BackendSchnorrAGMHashDispatchLocalCost

/-! Selector and rejection costs for the all-shape hash dispatcher. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.HashDispatch

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  (mono : Monotone overhead)

include sizes in
omit [Q.HasCategory] QP QS [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem route_property (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input) :
    Sum.elim (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap)
      (Hash.Input (Q := Q) rep width cap historyWidth basisCap coeffCap) (routeValue input) := by
  have h := decoded_property rep sizes width cap historyWidth basisCap groupCap rowCap coeffCap hh hg input hi
  dsimp only [routeValue]
  split <;> exact h

include sizes lists in
omit [Q.HasCategory] QP QS [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
theorem route_size (width cap historyWidth basisCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input) :
    Q.size (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) (routeValue input) ≤
      2 * frameWidth width cap historyWidth groupCap rowCap coeffCap := by
  have hp := prepare_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf hg input hi
  have hv := (sizes.snd_le rep.data.bool (rep.ty Hash.inputTy) (prepareValue input)).trans hp
  have hs := sizes.sum_le (rep.ty Hash.inputTy) (rep.ty Hash.inputTy) (routeValue input)
  have hw : width ≤ frameWidth width cap historyWidth groupCap rowCap coeffCap := by
    have h := Nat.mul_le_mul_right width (show 1 ≤
      4 * groupCap + 4 * rowCap * (coeffCap + 1) + 4 * coeffCap + 128 by omega)
    dsimp only [frameWidth]
    omega
  cases hflag : (prepareValue input).1 <;>
    simp only [routeValue, hflag, Bool.false_eq_true, ↓reduceIte, Sum.elim] at hs ⊢ <;> omega

include sizes lists laws dataLaws mono in
theorem route_cost (width cap historyWidth basisCap groupCap rowCap coeffCap pointZeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hz : (primitiveBound .zero₁).time () ≤ pointZeroTime)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap historyWidth basisCap groupCap rowCap coeffCap input) :
    Q.cost (route rep data cost primitive) input ≤
      prepareTime overhead (frameWidth width cap historyWidth groupCap rowCap coeffCap) groupCap rowCap pointZeroTime +
        2 * overhead (4096 * frameWidth width cap historyWidth groupCap rowCap coeffCap) := by
  let W := frameWidth width cap historyWidth groupCap rowCap coeffCap
  have hin := (input_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf input hi).1
  have hp := prepare_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf hg input hi
  have hr := route_size rep sizes lists width cap historyWidth basisCap groupCap rowCap coeffCap hh hu hb hf hg input hi
  have ht := prepare_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    width cap historyWidth basisCap groupCap rowCap coeffCap pointZeroTime hh hu hb hf hg hz input hi
  have hsel := dataLaws.select (rep.ty Hash.inputTy) (prepareValue input)
  change Q.cost (data.select (rep.ty Hash.inputTy)) (prepareValue input) ≤
    overhead (Q.size (rep.ty preparedTy) (prepareValue input) +
      Q.size (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) (routeValue input)) at hsel
  have hc := laws.compose (prepare rep data cost primitive) (data.select (rep.ty Hash.inputTy)) input
  change Q.cost (route rep data cost primitive) input ≤ Q.cost (prepare rep data cost primitive) input +
    Q.cost (data.select (rep.ty Hash.inputTy)) (prepareValue input) +
    overhead (Q.size (rep.ty inputTy) input + Q.size (rep.ty preparedTy) (prepareValue input) +
      Q.size (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) (routeValue input)) at hc
  have hs := hsel.trans (mono (show Q.size (rep.ty preparedTy) (prepareValue input) +
    Q.size (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) (routeValue input) ≤ 4096 * W by omega))
  have hj := mono (show Q.size (rep.ty inputTy) input + Q.size (rep.ty preparedTy) (prepareValue input) +
    Q.size (StepClass.HasSum.sum (rep.ty Hash.inputTy) (rep.ty Hash.inputTy)) (routeValue input) ≤ 4096 * W by omega)
  exact hc.trans (by dsimp only [W] at *; omega)

include sizes laws dataLaws mono in
theorem reject_cost (input : Hash.inputTy.Value (cryptoBase F G₁ G₂ K M)) (width fieldTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.ty Hash.inputTy) input ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime) :
    Q.cost (reject rep data cost primitive) input ≤ fieldTime + 516 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty Read.outputTy) (rejectValue input) ≤ 32 * width := by
    dsimp only [rejectValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive rejectExpression)
      (input, ()) ≤ fieldTime + 512 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound rejectExpression (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [rejectExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.boolBound, Expr.denote, Var.get, arithmetic,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  rw [reject, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono rejectExpression input width
    (fieldTime + 512 * overhead (256 * width)) hh hu hi hout he
  exact h.trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native.HashDispatch
