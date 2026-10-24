import Proofs.Runtime.BackendSchnorrAGMRandomSize

/-! Compiled local costs for marking random requests and constructing replies.
No field/group operation or whole-handler efficiency assumption is needed. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Random

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
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hi : Q.size (rep.env [inputTy]) (input, ()) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound scan).time (input.1, input, ()) ≤ time) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (prepareWith scan)).time (input, ()) ≤ time + 1024 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hleft := sizes.sum_le (rep.env [.bool, .list point₁, inputTy]) (rep.env [.bool, .list point₁, inputTy])
    (.inl (scan.denote (arithmetic F G₁ G₂ K M cost) (input.1, input, ()), input.1, input, ()))
  have hright := sizes.sum_le (rep.env [.bool, .list point₁, inputTy]) (rep.env [.bool, .list point₁, inputTy])
    (.inr (scan.denote (arithmetic F G₁ G₂ K M cost) (input.1, input, ()), input.1, input, ()))
  dsimp only [Sum.elim] at hleft hright
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  cases hflag : scan.denote (arithmetic F G₁ G₂ K M cost) (input.1, input, ()) <;>
    dsimp only [prepareWith, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.castFunction, LocalBound.elim, DataCostLaws.unitBound, DataCostLaws.boolBound,
      DataCostLaws.selectBound, Expr.denote, Var.get, id, Function.comp_def, Sum.elim] <;>
    simp only [hflag, Bool.false_eq_true, ↓reduceIte] <;>
    dsimp only [LanguageRepresentation.ty, LanguageRepresentation.env] at * <;> grind only

def prepareTime (overhead : Nat → Nat) (width groupCap : Nat) : Nat :=
  ListEmpty.scanTime overhead width groupCap + 1028 * overhead (256 * width)

include laws dataLaws lists in
theorem prepare_cost (width cap basisCap signedCap groupCap rowCap coeffCap arityCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hn : ∀ n ≤ arityCap, Q.size rep.data.nat n ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (hi : Input (Q := Q) rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap input) :
    Q.cost (prepare rep data cost primitive) input ≤
      prepareTime overhead (frameWidth width cap basisCap signedCap groupCap rowCap coeffCap) groupCap := by
  let W := frameWidth width cap basisCap signedCap groupCap rowCap coeffCap
  have hw : width ≤ W := calc
    width ≤ Signing.frameWidth width cap basisCap signedCap := by dsimp [Signing.frameWidth]; nlinarith
    _ ≤ W := Nat.le_add_right _ _
  have hin := input_size rep sizes lists width cap basisCap signedCap groupCap rowCap coeffCap arityCap hh hu hb hf hg hn input hi
  have hs := ListEmpty.scan_time rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
    sizes lists mono (cell := point₁) (Γ := [inputTy]) input.1 (input, ()) W groupCap
    (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) hin.2 (fun g _ => (hg g).trans hw) hi.groups
  have he := prepareWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    ListEmpty.scan input W (ListEmpty.scanTime overhead W groupCap) (hh.trans hw) (hu.trans hw)
    (fun b => (hb b).trans hw) hin.2 hs
  have hexpr := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound prepareExpression (input, ())).trans he
  have hout := prepared_size rep sizes lists width cap basisCap signedCap arityCap hh hb hf hn (prepareValue input)
    (prepare_property rep width cap basisCap signedCap groupCap rowCap coeffCap arityCap input hi)
  have hcore : Signing.frameWidth width cap basisCap signedCap ≤ W := Nat.le_add_right _ _
  rw [prepare, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono prepareExpression input W
    _ (hh.trans hw) (hu.trans hw) hin.1
    (by rw [prepareExpression_value]; exact hout.trans (by omega)) hexpr
  exact h.trans (by dsimp only [prepareTime, W]; omega)

include laws dataLaws lists in
theorem wrap_cost (input : preparedTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty preparedTy) input ≤ width) :
    Q.cost (wrap rep data cost primitive) input ≤ 260 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := lists.nil_le (rep.ty point₁)
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
      DataCostLaws.unitBound, DataCostLaws.nilBound, Expr.denote, Var.get,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  rw [wrap, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono wrapExpression input width
    (256 * overhead (256 * width)) hh hu hi hout he
  exact h.trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native.Random
