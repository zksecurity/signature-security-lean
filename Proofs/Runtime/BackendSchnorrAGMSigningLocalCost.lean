import Proofs.Runtime.BackendSchnorrAGMSigningSize

/-! Derived native costs for signing's arithmetic and history adapters. The
list appends are compiled traversals; no completed adapter budget is assumed. -/

open PFunctor

namespace Signatures.Runtime.SchnorrAGM.Native.Signing

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

include sizes laws dataLaws mono

theorem prepare_cost (input : sampledTy.Value (cryptoBase F G₁ G₂ K M))
    (width fieldTime scaleTime groupTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width) (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (hi : Q.size (rep.ty sampledTy) input ≤ width)
    (hz : (primitiveBound .zero).time () ≤ fieldTime)
    (hn : ∀ f : F, (primitiveBound .neg).time f ≤ fieldTime)
    (hs : ∀ f : F, ∀ g : G₁, (primitiveBound .scale₁).time (f, g) ≤ scaleTime)
    (hd : ∀ g h : G₁, (primitiveBound .sub₁).time (g, h) ≤ groupTime) :
    Q.cost (prepare rep data cost primitive) input ≤
      2 * fieldTime + 2 * scaleTime + groupTime + 1028 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty workTy) (arithmeticValue input) ≤ 32 * width := by
    dsimp only [arithmeticValue, LanguageRepresentation.ty, workTy, cacheArgsTy, replyTy, affineTy] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive arithmeticExpression)
      (input, ()) ≤ 2 * fieldTime + 2 * scaleTime + groupTime + 1024 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound arithmeticExpression (input, ())).trans ?_
    have hneg := hn input.1.1
    have hscale₁ := hs input.1.2 input.2.1
    have hscale₂ := hs input.1.1 input.2.2.1
    have hsub := hd (input.1.2 • input.2.1) (input.1.1 • input.2.2.1)
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ h => mono h
    dsimp only [arithmeticExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.unitBound, DataCostLaws.boolBound, Expr.denote, Var.get, arithmetic,
      id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  rw [prepare, QuantitativeStepClass.Realizer.cost_castFunction]
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono arithmeticExpression input width
    (2 * fieldTime + 2 * scaleTime + groupTime + 1024 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

private theorem historiesWith_time
    (signed : Expr CryptoOp [message, .list message, workTy] (.list message))
    (basis : Expr CryptoOp [affineTy, .list affineTy, .list message, message, .list message, workTy] (.list affineTy))
    (input : workTy.Value (cryptoBase F G₁ G₂ K M)) (width signedTime basisTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty workTy) input ≤ width)
    (hm : Q.size (rep.ty (.list message))
      (signed.denote (arithmetic F G₁ G₂ K M cost) (input.2.2.2.1, input.2.2.2.2.2.1, input, ())) ≤ width)
    (ha : Q.size (rep.ty (.list affineTy))
      (basis.denote (arithmetic F G₁ G₂ K M cost)
        (input.2.2.1, input.2.2.2.2.1,
          signed.denote (arithmetic F G₁ G₂ K M cost) (input.2.2.2.1, input.2.2.2.2.2.1, input, ()),
          input.2.2.2.1, input.2.2.2.2.2.1, input, ())) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound signed).time
      (input.2.2.2.1, input.2.2.2.2.2.1, input, ()) ≤ signedTime)
    (hb : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound basis).time
      (input.2.2.1, input.2.2.2.2.1,
        signed.denote (arithmetic F G₁ G₂ K M cost) (input.2.2.2.1, input.2.2.2.2.2.1, input, ()),
        input.2.2.2.1, input.2.2.2.2.2.1, input, ()) ≤ basisTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (historiesWith signed basis)).time (input, ()) ≤ signedTime + basisTime + 512 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ h => mono h
  dsimp only [historiesWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    Expr.denote, Var.get, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

include lists primitiveBound in
theorem histories_cost (width cap basisCap signedCap : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (input : workTy.Value (cryptoBase F G₁ G₂ K M)) (hi : Work (Q := Q) rep width cap basisCap signedCap input) :
    Q.cost (histories rep data cost primitive) input ≤
      ListSnoc.snocTime overhead (16 * frameWidth width cap basisCap signedCap) signedCap +
      ListSnoc.snocTime overhead (16 * frameWidth width cap basisCap signedCap) basisCap +
        516 * overhead (256 * frameWidth width cap basisCap signedCap) := by
  let W := frameWidth width cap basisCap signedCap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hin := work_size rep sizes lists width cap basisCap signedCap hh hu hb hf input hi
  have hout := programInput_size rep sizes lists width cap basisCap signedCap hh hu hb hf (historiesValue input)
    (histories_property rep width cap basisCap signedCap input hi)
  have hm : ∀ m ∈ input.2.2.2.2.2.1 ++ [input.2.2.2.1], Q.size (rep.ty message) m ≤ width := by
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hi.history.signed m hm
    · simpa only [List.mem_singleton.mp hm] using hi.message
  have hmsg := lists.size_le_cap (rep.ty message) (input.2.2.2.2.2.1 ++ [input.2.2.2.1])
    width (signedCap + 1) hm (by simp only [List.length_append, List.length_singleton]; exact Nat.add_le_add_right hi.history.signedLength 1)
  have hmsg' : Q.size (rep.ty (.list message)) (input.2.2.2.2.2.1 ++ [input.2.2.2.1]) ≤ W := by
    change Q.size (rep.ty (.list message)) _ ≤ _ at hmsg
    dsimp [W, frameWidth]
    nlinarith [Nat.mul_le_mul_left (signedCap + 1) hh]
  have hbasis := lists.size_le_cap (rep.ty affineTy) (input.2.2.2.2.1 ++ [input.2.2.1])
    (3 * width) (basisCap + 1) (fun a _ => affine_size rep sizes width hh hf a)
    (by simp only [List.length_append, List.length_singleton]; exact Nat.add_le_add_right hi.history.basisLength 1)
  have hbasis' : Q.size (rep.ty (.list affineTy)) (input.2.2.2.2.1 ++ [input.2.2.1]) ≤ W := by
    change Q.size (rep.ty (.list affineTy)) _ ≤ _ at hbasis
    dsimp [W, frameWidth]
    nlinarith [Nat.mul_le_mul_left (basisCap + 1) hh]
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcontext₁ : Q.size (rep.env [workTy]) (input, ()) ≤ 16 * W := by
    dsimp only [LanguageRepresentation.env] at *
    grind only
  have hcontext₂ : Q.size (rep.env [.list message, message, .list message, workTy])
      (input.2.2.2.2.2.1 ++ [input.2.2.2.1], input.2.2.2.1, input.2.2.2.2.2.1, input, ()) ≤ 16 * W := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have hfirst := ListSnoc.expression_time (cell := message) (Γ := [workTy])
    rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes lists mono
    input.2.2.2.1 input.2.2.2.2.2.1 (input, ()) (16 * W) signedCap
    (by omega) (by omega) hcontext₁ (hi.message.trans (by omega))
    (fun m hm => (hi.history.signed m hm).trans (by omega)) hi.history.signedLength
  have hsecond := ListSnoc.expression_time (cell := affineTy) (Γ := [.list message, message, .list message, workTy])
    rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes lists mono
    input.2.2.1 input.2.2.2.2.1
    (input.2.2.2.2.2.1 ++ [input.2.2.2.1], input.2.2.2.1, input.2.2.2.2.2.1, input, ()) (16 * W) basisCap
    (by omega) (by omega) hcontext₂ (hi.affine.trans (by omega))
    (fun a _ => (affine_size rep sizes width hh hf a).trans (by omega)) hi.history.basisLength
  have hdenote := ListSnoc.denote (cell := message) (Γ := [workTy])
    (arithmetic F G₁ G₂ K M cost) input.2.2.2.1 input.2.2.2.2.2.1 (input, ())
  have ht := historiesWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    ListSnoc.expression ListSnoc.expression input W
    (ListSnoc.snocTime overhead (16 * W) signedCap) (ListSnoc.snocTime overhead (16 * W) basisCap)
    (hh.trans hw) (hu.trans hw) hin (by rw [ListSnoc.denote]; exact hmsg')
    (by rw [ListSnoc.denote]; exact hbasis') hfirst (by rw [hdenote]; exact hsecond)
  have he := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound historiesExpression (input, ())).trans ht
  rw [histories, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := Read.framed_cost rep data cost primitive sizes laws dataLaws mono historiesExpression input W
    (ListSnoc.snocTime overhead (16 * W) signedCap + ListSnoc.snocTime overhead (16 * W) basisCap +
      512 * overhead (256 * W)) (hh.trans hw) (hu.trans hw) hin
    (by rw [historiesExpression_value]; exact hout.trans (by omega)) he
  exact h.trans (by dsimp only [W] at *; omega)

include primitiveBound in
theorem finish_cost (input : programOutputTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty programOutputTy) input ≤ width) :
    Q.cost (finish rep data cost primitive) input ≤ 260 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty outputTy) (returnValue input) ≤ 32 * width := by
    dsimp only [returnValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive returnExpression)
      (input, ()) ≤ 256 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound returnExpression (input, ())).trans ?_
    have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ h => mono h
    dsimp only [returnExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      Expr.denote, Var.get, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  rw [finish, QuantitativeStepClass.Realizer.cost_castFunction]
  exact (Read.framed_cost rep data cost primitive sizes laws dataLaws mono returnExpression input width
    (256 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

end Signatures.Runtime.SchnorrAGM.Native.Signing
