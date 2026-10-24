import Proofs.Runtime.BackendSchnorrRawChallengeSize
import Proofs.Runtime.BackendSchnorrRawUniformLocalCost
import Proofs.Runtime.BackendSeedTapeScanCost

/-! Derived costs for the native challenge scan and chronological save. Every
retained list and expression context is charged by the shared scan/append proofs. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeChallenge

open BackendProgram

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))

private def prepareWith
    (scan : Expr CryptoOp [.nat, .list Replay.Mixed.event, stateTy] SeedTape.popState) :
    Expr CryptoOp [stateTy] prepareTy :=
  .letE (.snd v0) (.letE (.nat 1) (.letE scan
    (.pair (.fst v0) (.pair (.fst (.snd (.fst (.snd v0))))
      (.pair (.fst v3) (.branch (.fst v0) (.snd (.snd v0)) (.snd v3)))))))

private def saveWith
    (append : Expr CryptoOp [Replay.Mixed.event, .list Replay.Mixed.event, drawTy]
      (.list Replay.Mixed.event)) : Expr CryptoOp [drawTy] drawTy :=
  .letE (.fst (.snd v0))
    (.letE (.pair (.nat 1) (.pair (.fst v1) (.nat 0)))
      (.letE append (.pair (.fst v3) (.pair v0 (.snd (.snd v3))))))

def prepareTime (overhead : Nat → Nat) (width savedCap remainingCap comparisonTime zeroTime : Nat) : Nat :=
  let W := NativeUniform.saveFrameWidth width savedCap remainingCap
  SeedTape.NativeScan.scanTime overhead W remainingCap comparisonTime zeroTime + 516 * overhead (256 * W)

def saveTime (overhead : Nat → Nat) (width savedCap remainingCap : Nat) : Nat :=
  let W := NativeUniform.saveFrameWidth width savedCap remainingCap
  ListSnoc.snocTime overhead (16 * W) savedCap + 516 * overhead (256 * W)

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

include sizes mono

private theorem prepareWith_time
    (scan : Expr CryptoOp [.nat, .list Replay.Mixed.event, stateTy] SeedTape.popState)
    (state : stateTy.Value (cryptoBase F G₁ G₂ K M)) (width scanTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty stateTy) state ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hs : Q.size (rep.ty SeedTape.popState)
      (scan.denote (arithmetic F G₁ G₂ K M cost) (1, state.2, state, ())) ≤ width)
    (hscan : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound scan).time (1, state.2, state, ()) ≤ scanTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (prepareWith scan)).time (state, ()) ≤ scanTime + 512 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  by_cases found : (scan.denote (arithmetic F G₁ G₂ K M cost) (1, state.2, state, ())).1 = true <;>
    dsimp only [prepareWith, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.elim, LocalBound.castFunction, DataCostLaws.selectBound, DataCostLaws.unitBound,
      DataCostLaws.natBound, Expr.denote, Var.get, LanguageRepresentation.ty, LanguageRepresentation.env,
      id, Function.comp_def, Sum.elim] at * <;>
    simp only [found, ↓reduceIte] <;>
    grind only

private theorem saveWith_time
    (append : Expr CryptoOp [Replay.Mixed.event, .list Replay.Mixed.event, drawTy]
      (.list Replay.Mixed.event))
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M)) (width appendTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hi : Q.size (rep.ty drawTy) input ≤ width)
    (ho : Q.size (rep.ty (.list Replay.Mixed.event))
      (append.denote (arithmetic F G₁ G₂ K M cost) ((1, input.1, 0), input.2.1, input, ())) ≤ width)
    (happend : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound append).time ((1, input.1, 0), input.2.1, input, ()) ≤ appendTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (saveWith append)).time (input, ()) ≤ appendTime + 512 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [saveWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.unitBound, DataCostLaws.natBound, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def] at *
  grind only

include lists laws dataLaws in
theorem prepare_cost (width savedCap remainingCap comparisonTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (state : stateTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : NativeUniform.StateBound (Q := Q) rep width savedCap remainingCap state)
    (hcompare : ∀ x ∈ state.2, (primitiveBound .natEq).time (x.1, 1) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (prepare rep data cost primitive) state ≤
      prepareTime overhead width savedCap remainingCap comparisonTime zeroTime := by
  let W := NativeUniform.saveFrameWidth width savedCap remainingCap
  have hw : width ≤ W := by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith
  have hin : Q.size (rep.ty stateTy) state ≤ W :=
    (NativeUniform.state_size rep sizes lists width savedCap remainingCap hh state bound).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
  have hout : Q.size (rep.ty prepareTy) (prepareValue state) ≤ W :=
    (prepare_size rep sizes lists width savedCap remainingCap hh hb hz state bound).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
  have hd := NativeUniform.cell_size rep sizes width hh (0, (0 : F), 0) ⟨hn0, hz, hn0⟩
  have hp := @sizes.prod_le
  have hcontext : Q.size (rep.env [stateTy]) (state, ()) ≤ W := by
    have hi := NativeUniform.state_size rep sizes lists width savedCap remainingCap hh state bound
    dsimp only [LanguageRepresentation.env, W, NativeUniform.saveFrameWidth] at *
    grind only
  have hs := SeedTape.NativeScan.scan_time (Γ := [stateTy]) rep data cost primitive laws dataLaws primitiveBound
    sizes lists mono 1 state.2 (state, ()) W remainingCap comparisonTime zeroTime
    (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (hn1.trans hw) hcontext
    (hd.trans (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith))
    (fun x member => (NativeUniform.cell_size rep sizes width hh x (bound.2.1 x member)).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)) bound.2.2 hcompare hzero
  have hdenote := (Expr.weakenTail_denote (Δ := [stateTy]) (arithmetic F G₁ G₂ K M cost)
    SeedTape.popCode (1, state.2, ()) (state, ())).trans (SeedTape.popCode_denote cost 1 state.2)
  simp only [Env.append] at hdenote
  have hcell : NativeUniform.CellBound (Q := Q) rep width (SeedTape.pop 1 (0, (0 : F), 0) state.2).2.1 := by
    rcases SeedTape.pop_answer_mem_or_default 1 (0, (0 : F), 0) state.2 with member | same
    · exact bound.2.1 _ member
    · rw [same]; exact ⟨hn0, hz, hn0⟩
  have hcellSize := NativeUniform.cell_size rep sizes width hh _ hcell
  have hrestSize := NativeUniform.tape_size rep sizes lists width remainingCap hh _
    (NativeUniform.pop_property rep width remainingCap 1 (0, (0 : F), 0) state.2 bound.2).1
  have hscanSize : Q.size (rep.ty SeedTape.popState)
      ((SeedTape.popCode.weakenTail [stateTy]).denote (arithmetic F G₁ G₂ K M cost)
        (1, state.2, state, ())) ≤ W := by
    rw [hdenote]
    dsimp only [LanguageRepresentation.ty, W, NativeUniform.saveFrameWidth] at *
    grind only
  have ht := prepareWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    (SeedTape.popCode.weakenTail [stateTy]) state W
    (SeedTape.NativeScan.scanTime overhead W remainingCap comparisonTime zeroTime)
    (hh.trans hw) (hu.trans hw) hin (hn1.trans hw) hscanSize hs
  have he := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound prepareExpression (state, ())).trans ht
  rw [prepare, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono prepareExpression state W
    (SeedTape.NativeScan.scanTime overhead W remainingCap comparisonTime zeroTime + 512 * overhead (256 * W))
    (hh.trans hw) (hu.trans hw) hin (by rw [prepareExpression_value]; exact hout.trans (by omega)) he
  exact h.trans (by dsimp only [prepareTime, W] at *; omega)

include lists laws dataLaws in
theorem save_cost (width savedCap remainingCap : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (input : drawTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : Output (Q := Q) rep width savedCap remainingCap input) :
    Q.cost (save rep data cost primitive) input ≤ saveTime overhead width savedCap remainingCap := by
  let primitiveBound : {a b : Ty CryptoAtom} → (op : CryptoOp a b) → LocalBound (primitive op) :=
    fun op => LocalBound.measured (primitive op)
  let W := NativeUniform.saveFrameWidth width savedCap remainingCap
  have hw : width ≤ W := by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith
  have hin : Q.size (rep.ty drawTy) input ≤ W :=
    (output_size rep sizes lists width savedCap remainingCap hh input bound).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
  have result := save_property rep width savedCap remainingCap hn0 hn1 input bound
  have hout : Q.size (rep.ty drawTy) (saveValue input) ≤ W :=
    (output_size rep sizes lists width (savedCap + 1) remainingCap hh (saveValue input) result).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
  have happend : Q.size (rep.ty (.list Replay.Mixed.event)) (input.2.1 ++ [(1, input.1, 0)]) ≤ W :=
    (NativeUniform.tape_size rep sizes lists width (savedCap + 1) hh _ result.2.1).trans
      (by dsimp [W, NativeUniform.saveFrameWidth]; nlinarith)
  have hcell := NativeUniform.cell_size rep sizes width hh (1, input.1, 0) ⟨hn1, bound.1, hn0⟩
  have hp := @sizes.prod_le
  have henv : Q.size (rep.env [drawTy]) (input, ()) ≤ 16 * W := by
    dsimp only [LanguageRepresentation.env] at *
    grind only
  have hsnoc := ListSnoc.expression_time (cell := Replay.Mixed.event) (Γ := [drawTy])
    rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound sizes lists mono
    (1, input.1, 0) input.2.1 (input, ()) (16 * W) savedCap
    (by omega) (by omega) henv (hcell.trans (by omega))
    (fun cell member => (NativeUniform.cell_size rep sizes width hh cell (bound.2.1.1 cell member)).trans (by omega))
    bound.2.1.2
  have ht := saveWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    ListSnoc.expression input W (ListSnoc.snocTime overhead (16 * W) savedCap)
    (hh.trans hw) (hu.trans hw) (hn0.trans hw) (hn1.trans hw) hin
    (by rw [ListSnoc.denote]; exact happend) hsnoc
  have he := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound saveExpression (input, ())).trans ht
  rw [save, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono saveExpression input W
    (ListSnoc.snocTime overhead (16 * W) savedCap + 512 * overhead (256 * W))
    (hh.trans hw) (hu.trans hw) hin (by rw [saveExpression_value]; exact hout.trans (by omega)) he
  exact h.trans (by dsimp only [saveTime, W] at *; omega)

end Signatures.Runtime.Schnorr.RawTape.NativeChallenge
