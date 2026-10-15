import Signatures.Runtime.BackendSchnorrAGMSigningDispatchSize

/-! Signing dispatch costs include the group scan, retained request data, and
construction of both accepted and rejected scalar/group-list replies. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.SigningDispatch

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

include sizes mono primitiveBound

private theorem prepareWith_time (scan : Expr CryptoOp [.list point₁, inputTy] .bool)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (width time : Nat)
    (hh : header ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.env [inputTy]) (input, ()) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound scan).time (input.1, input, ()) ≤ time) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (prepareWith scan)).time (input, ()) ≤ time + 128 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [prepareWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env,
    id, Function.comp_def] at *
  grind only

def prepareTime (overhead : Nat → Nat) (width groupCap : Nat) : Nat :=
  ListEmpty.scanTime overhead width groupCap + 132 * overhead (256 * width)

include laws dataLaws lists in
theorem prepare_cost (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap input) :
    Q.cost (prepare rep data cost primitive) input ≤
      prepareTime overhead (frameWidth width cap basisCap signedCap groupCap rowCap coeffCap) groupCap := by
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  have hw : width ≤ W := calc
    width ≤ Signing.frameWidth width cap basisCap signedCap := by dsimp [Signing.frameWidth]; nlinarith
    _ ≤ W := Nat.le_add_right _ _
  have hin := input_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap hh hu hb hf hg input hi
  have hs := ListEmpty.scan_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    sizes lists mono (cell := point₁) (Γ := [inputTy]) input.1 (input, ()) W groupCap
    (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) hin.2 (fun g _ => (hg g).trans hw) hi.groups
  have he := prepareWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    ListEmpty.scan input W (ListEmpty.scanTime overhead W groupCap) (hh.trans hw)
    (fun b => (hb b).trans hw) hin.2 hs
  have hexpr := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound prepareExpression (input, ())).trans he
  have hout := prepare_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap hh hb hf input hi
  rw [prepare, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono prepareExpression input W
    _ (hh.trans hw) (hu.trans hw) hin.1
    (by rw [prepareExpression_value]; exact hout.trans (by omega)) hexpr
  exact h.trans (by dsimp only [prepareTime, W]; omega)

include laws dataLaws lists in
theorem route_cost (width cap basisCap signedCap groupCap rowCap coeffCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap input) :
    Q.cost (route rep data cost primitive) input ≤
      prepareTime overhead (frameWidth width cap basisCap signedCap groupCap rowCap coeffCap) groupCap +
        2 * overhead (256 * frameWidth width cap basisCap signedCap groupCap rowCap coeffCap) := by
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  have hin := (input_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap hh hu hb hf hg input hi).1
  have hp := prepare_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap hh hb hf input hi
  have hr := route_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap hh hb hf input hi
  have ht := prepare_cost rep data cost primitive sizes lists laws dataLaws primitiveBound mono
    width cap basisCap signedCap groupCap rowCap coeffCap hh hu hb hf hg input hi
  have hsel := dataLaws.select (rep.ty Signing.inputTy) (prepareValue input)
  change Q.cost (data.select (rep.ty Signing.inputTy)) (prepareValue input) ≤
    overhead (Q.size (rep.ty preparedTy) (prepareValue input) +
      Q.size (StepClass.HasSum.sum (rep.ty Signing.inputTy) (rep.ty Signing.inputTy)) (routeValue input)) at hsel
  have hc := laws.compose (prepare rep data cost primitive) (data.select (rep.ty Signing.inputTy)) input
  change Q.cost (route rep data cost primitive) input ≤ Q.cost (prepare rep data cost primitive) input +
    Q.cost (data.select (rep.ty Signing.inputTy)) (prepareValue input) +
    overhead (Q.size (rep.ty inputTy) input + Q.size (rep.ty preparedTy) (prepareValue input) +
      Q.size (StepClass.HasSum.sum (rep.ty Signing.inputTy) (rep.ty Signing.inputTy)) (routeValue input)) at hc
  have hfee : ∀ n ≤ 256 * W, overhead n ≤ overhead (256 * W) := fun _ hn => mono hn
  have hs := hsel.trans (hfee _ (by omega))
  have hj := hfee (Q.size (rep.ty inputTy) input + Q.size (rep.ty preparedTy) (prepareValue input) +
    Q.size (StepClass.HasSum.sum (rep.ty Signing.inputTy) (rep.ty Signing.inputTy)) (routeValue input)) (by omega)
  exact hc.trans (by dsimp only [W] at *; omega)

include laws dataLaws lists in
theorem wrap_cost (input : Signing.outputTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty Signing.outputTy) input ≤ width) :
    Q.cost (wrap rep data cost primitive) input ≤ 260 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := lists.nil_le (rep.ty point₁)
  have hcons := lists.cons_le (rep.ty point₁) input.1.1 []
  have hout : Q.size (rep.ty outputTy) (wrapValue input) ≤ 32 * width := by
    dsimp only [wrapValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive wrapExpression)
      (input, ()) ≤ 256 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound wrapExpression (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [wrapExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.nilBound, DataCostLaws.consBound, Expr.denote, Var.get,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  rw [wrap, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono wrapExpression input width
    (256 * overhead (256 * width)) hh hu hi hout he
  exact h.trans (by omega)

include laws dataLaws lists in
theorem reject_cost (input : Signing.inputTy.Value (cryptoBase F G₁ G₂ K M)) (width fieldTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.ty Signing.inputTy) input ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime) :
    Q.cost (reject rep data cost primitive) input ≤ fieldTime + 516 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := lists.nil_le (rep.ty point₁)
  have hout : Q.size (rep.ty outputTy) (rejectValue input) ≤ 32 * width := by
    dsimp only [rejectValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive rejectExpression)
      (input, ()) ≤ fieldTime + 512 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound rejectExpression (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
    dsimp only [rejectExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.boolBound, DataCostLaws.nilBound, Expr.denote, Var.get, arithmetic,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  rw [reject, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono rejectExpression input width
    (fieldTime + 512 * overhead (256 * width)) hh hu hi hout he
  exact h.trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native.SigningDispatch
