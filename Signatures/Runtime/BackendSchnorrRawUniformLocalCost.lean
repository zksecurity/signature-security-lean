import Signatures.Runtime.BackendSchnorrRawUniformSize
import Signatures.Runtime.BackendListSnoc

/-! Native return and chronological-save costs for a raw private draw. The save
bound charges both append traversals, construction of the fresh cell, and the
entire retained input, including both tape lists. Scan costs are separate. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeUniform

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

include primitiveBound in
theorem hit_cost (input : drawTy.Value (cryptoBase F G₁ G₂ K M)) (width : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty drawTy) input ≤ width) :
    Q.cost (hit rep data cost primitive) input ≤ 260 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hout : Q.size (rep.ty inputTy) (hitValue input) ≤ 32 * width := by
    dsimp only [hitValue, LanguageRepresentation.ty] at *
    grind only
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive hitExpression)
      (input, ()) ≤ 256 * overhead (256 * width) := by
    refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound hitExpression (input, ())).trans ?_
    have hfee : ∀ k ≤ 256 * width, overhead k ≤ overhead (256 * width) := fun _ h => mono h
    dsimp only [hitExpression, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      Expr.denote, Var.get, id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
    grind only
  rw [hit, QuantitativeStepClass.Realizer.cost_castFunction]
  exact (framed_cost rep data cost primitive sizes laws dataLaws mono hitExpression input width
    (256 * overhead (256 * width)) hh hu hi hout he).trans (by omega)

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))

private def saveWith
    (append : Expr CryptoOp [Replay.Mixed.event, .list Replay.Mixed.event, drawTy]
      (.list Replay.Mixed.event)) : Expr CryptoOp [drawTy] inputTy :=
  .letE (.fst (.snd (.snd v0)))
    (.letE (.pair (.fst (.snd v1)) (.pair (.op .zero .unit) (.fst v1)))
      (.letE append (.pair (.fst v3) (.pair v0 (.snd (.snd (.snd v3)))))))

private theorem saveWith_time
    (append : Expr CryptoOp [Replay.Mixed.event, .list Replay.Mixed.event, drawTy]
      (.list Replay.Mixed.event))
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M)) (width zeroTime appendTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.ty drawTy) input ≤ width)
    (ho : Q.size (rep.ty (.list Replay.Mixed.event))
      (append.denote (arithmetic F G₁ G₂ K M cost)
        ((input.2.1, (0 : F), input.1), input.2.2.1, input, ())) ≤ width)
    (zeroCost : (primitiveBound .zero).time () ≤ zeroTime)
    (appendCost : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws
      dataLaws primitiveBound append).time
        ((input.2.1, (0 : F), input.1), input.2.2.1, input, ()) ≤ appendTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (saveWith append)).time (input, ()) ≤ zeroTime + appendTime + 512 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 256 * width, overhead k ≤ overhead (256 * width) := fun _ h => mono h
  dsimp only [saveWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.unitBound, Expr.denote, Var.get, arithmetic,
    id, Function.comp_def, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

def saveFrameWidth (width savedCap remainingCap : Nat) : Nat :=
  (6 * (savedCap + remainingCap) + 16) * width

def saveTime (overhead : Nat → Nat) (width savedCap remainingCap zeroTime : Nat) : Nat :=
  let W := saveFrameWidth width savedCap remainingCap
  zeroTime + ListSnoc.snocTime overhead (16 * W) savedCap + 516 * overhead (256 * W)

include lists in
theorem save_cost (width savedCap remainingCap zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (zeroCost : (primitiveBound .zero).time () ≤ zeroTime)
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : DrawBound (Q := Q) rep width savedCap remainingCap input) :
    Q.cost (save rep data cost primitive) input ≤ saveTime overhead width savedCap remainingCap zeroTime := by
  let W := saveFrameWidth width savedCap remainingCap
  have hw : width ≤ W := by dsimp [W, saveFrameWidth]; nlinarith
  have hin : Q.size (rep.ty drawTy) input ≤ W :=
    (draw_size rep sizes lists width savedCap remainingCap hh input bound).trans
      (by dsimp [W, saveFrameWidth]; nlinarith)
  have result := save_property rep width savedCap remainingCap hz input bound
  have hout : Q.size (rep.ty inputTy) (saveValue input) ≤ W :=
    (input_size rep sizes lists width (savedCap + 1) remainingCap hh (saveValue input) result).trans
      (by dsimp [W, saveFrameWidth]; nlinarith)
  have happend : Q.size (rep.ty (.list Replay.Mixed.event))
      (input.2.2.1 ++ [(input.2.1, (0 : F), input.1)]) ≤ W :=
    (tape_size rep sizes lists width (savedCap + 1) hh _ result.2.1).trans
      (by dsimp [W, saveFrameWidth]; nlinarith)
  have hcell := cell_size rep sizes width hh (input.2.1, (0 : F), input.1) ⟨bound.2.1, hz, bound.1⟩
  have hp := @sizes.prod_le
  have henv : Q.size (rep.env [drawTy]) (input, ()) ≤ 16 * W := by
    dsimp only [LanguageRepresentation.env] at *
    grind only
  have hsnoc := ListSnoc.expression_time (cell := Replay.Mixed.event) (Γ := [drawTy])
    rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes lists mono
    (input.2.1, (0 : F), input.1) input.2.2.1 (input, ()) (16 * W) savedCap
    (by omega) (by omega) henv (hcell.trans (by omega))
    (fun cell member => (cell_size rep sizes width hh cell (bound.2.2.1.1 cell member)).trans (by omega))
    bound.2.2.1.2
  have ht := saveWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    ListSnoc.expression input W zeroTime (ListSnoc.snocTime overhead (16 * W) savedCap)
    (hh.trans hw) (hu.trans hw) (hz.trans hw) hin
    (by rw [ListSnoc.denote]; exact happend) zeroCost hsnoc
  have he := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound saveExpression (input, ())).trans ht
  rw [save, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := framed_cost rep data cost primitive sizes laws dataLaws mono saveExpression input W
    (zeroTime + ListSnoc.snocTime overhead (16 * W) savedCap + 512 * overhead (256 * W))
    (hh.trans hw) (hu.trans hw) hin
    (by rw [saveExpression_value]; exact hout.trans (by omega)) he
  exact h.trans (by dsimp only [saveTime, W] at *; omega)

end Signatures.Runtime.Schnorr.RawTape.NativeUniform
