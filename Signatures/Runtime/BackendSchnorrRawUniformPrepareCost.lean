import Signatures.Runtime.BackendSchnorrRawUniformLocalCost
import Signatures.Runtime.BackendSeedTapeScanCost

/-! Native private-draw preparation costs. The actual retained-context scan is
charged from its fold/reverse implementation; only primitive costs are inputs. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeUniform

open BackendProgram

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v3 {a b c d Γ} : Expr CryptoOp (a :: b :: c :: d :: Γ) d :=
  .var (.there (.there (.there .here)))

private def prepareWith
    (scan : Expr CryptoOp [.nat, .list Replay.Mixed.event, inputTy] SeedTape.popState) :
    Expr CryptoOp [inputTy] prepareTy :=
  .letE (.snd (.snd v0))
    (.letE (.op .natAdd (.pair (.fst v1) (.nat 2)))
      (.letE scan
        (.pair (.fst v0)
          (.pair (.branch (.fst v0) (.snd (.snd (.fst (.snd v0)))) (.fst v3))
            (.pair v1 (.pair (.fst (.snd v3))
              (.branch (.fst v0) (.snd (.snd v0)) (.snd (.snd v3)))))))))

def prepareTime (overhead : Nat → Nat)
    (width savedCap remainingCap comparisonTime zeroTime addTime : Nat) : Nat :=
  let W := saveFrameWidth width savedCap remainingCap
  SeedTape.NativeScan.scanTime overhead W remainingCap comparisonTime zeroTime +
    addTime + 1028 * overhead (256 * W)

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
    (scan : Expr CryptoOp [.nat, .list Replay.Mixed.event, inputTy] SeedTape.popState)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (width scanTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.ty inputTy) input ≤ width)
    (htwo : Q.size rep.data.nat 2 ≤ width)
    (htag : Q.size rep.data.nat (input.1 + 2) ≤ width)
    (hs : Q.size (rep.ty SeedTape.popState)
      (scan.denote (arithmetic F G₁ G₂ K M cost) (input.1 + 2, input.2.2, input, ())) ≤ width)
    (hscan : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound scan).time (input.1 + 2, input.2.2, input, ()) ≤ scanTime)
    (hadd : (primitiveBound .natAdd).time (input.1, 2) ≤ addTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (prepareWith scan)).time (input, ()) ≤ scanTime + addTime + 1024 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hsum := @sizes.sum_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  by_cases found : (scan.denote (arithmetic F G₁ G₂ K M cost) (input.1 + 2, input.2.2, input, ())).1 = true <;>
    dsimp only [prepareWith, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      LocalBound.elim, LocalBound.castFunction, DataCostLaws.selectBound, DataCostLaws.unitBound,
      DataCostLaws.natBound, Expr.denote, Var.get, arithmetic,
      LanguageRepresentation.ty, LanguageRepresentation.env, id, Function.comp_def, Sum.elim] at * <;>
    simp only [found, ↓reduceIte] <;>
    grind only

include lists laws dataLaws in
theorem prepare_cost (width savedCap remainingCap comparisonTime zeroTime addTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn2 : Q.size rep.data.nat 2 ≤ width)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : InputBound (Q := Q) rep width savedCap remainingCap input)
    (htag : Q.size rep.data.nat (input.1 + 2) ≤ width)
    (hcompare : ∀ x ∈ input.2.2, (primitiveBound .natEq).time (x.1, input.1 + 2) ≤ comparisonTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (hadd : (primitiveBound .natAdd).time (input.1, 2) ≤ addTime) :
    Q.cost (prepare rep data cost primitive) input ≤
      prepareTime overhead width savedCap remainingCap comparisonTime zeroTime addTime := by
  let W := saveFrameWidth width savedCap remainingCap
  have hw : width ≤ W := by dsimp [W, saveFrameWidth]; nlinarith
  have hin : Q.size (rep.ty inputTy) input ≤ W :=
    (input_size rep sizes lists width savedCap remainingCap hh input bound).trans
      (by dsimp [W, saveFrameWidth]; nlinarith)
  have hout : Q.size (rep.ty prepareTy) (prepareValue input) ≤ W :=
    (prepare_size rep sizes lists width savedCap remainingCap hh hb input bound htag).trans
      (by dsimp [W, saveFrameWidth]; nlinarith)
  have hd := cell_size rep sizes width hh (0, (0 : F), 0) ⟨hn0, hz, hn0⟩
  have hp := @sizes.prod_le
  have hcontext : Q.size (rep.env [inputTy]) (input, ()) ≤ W := by
    have hi := input_size rep sizes lists width savedCap remainingCap hh input bound
    dsimp only [LanguageRepresentation.env, W, saveFrameWidth] at *
    grind only
  have hs := SeedTape.NativeScan.scan_time (Γ := [inputTy]) rep data cost primitive laws dataLaws primitiveBound
    sizes lists mono (input.1 + 2) input.2.2 (input, ()) W remainingCap comparisonTime zeroTime
    (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (htag.trans hw) hcontext
    (hd.trans (by dsimp [W, saveFrameWidth]; nlinarith))
    (fun x member => (cell_size rep sizes width hh x (bound.2.2.1 x member)).trans
      (by dsimp [W, saveFrameWidth]; nlinarith))
    bound.2.2.2 hcompare hzero
  have hdenote := (Expr.weakenTail_denote (Δ := [inputTy]) (arithmetic F G₁ G₂ K M cost)
    SeedTape.popCode (input.1 + 2, input.2.2, ()) (input, ())).trans
      (SeedTape.popCode_denote cost (input.1 + 2) input.2.2)
  simp only [Env.append] at hdenote
  have hcell : CellBound (Q := Q) rep width (SeedTape.pop (input.1 + 2) (0, (0 : F), 0) input.2.2).2.1 := by
    rcases SeedTape.pop_answer_mem_or_default (input.1 + 2) (0, (0 : F), 0) input.2.2 with member | same
    · exact bound.2.2.1 _ member
    · rw [same]; exact ⟨hn0, hz, hn0⟩
  have hcellSize := cell_size rep sizes width hh _ hcell
  have hrestSize := tape_size rep sizes lists width remainingCap hh _
    (pop_property rep width remainingCap (input.1 + 2) (0, (0 : F), 0) input.2.2 bound.2.2).1
  have hscanSize : Q.size (rep.ty SeedTape.popState)
      ((SeedTape.popCode.weakenTail [inputTy]).denote (arithmetic F G₁ G₂ K M cost)
        (input.1 + 2, input.2.2, input, ())) ≤ W := by
    rw [hdenote]
    dsimp only [LanguageRepresentation.ty, W, saveFrameWidth] at *
    grind only
  have ht := prepareWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    (SeedTape.popCode.weakenTail [inputTy]) input W
    (SeedTape.NativeScan.scanTime overhead W remainingCap comparisonTime zeroTime) addTime
    (hh.trans hw) (hu.trans hw) hin (hn2.trans hw) (htag.trans hw) hscanSize hs hadd
  have he := (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound prepareExpression (input, ())).trans ht
  rw [prepare, QuantitativeStepClass.Realizer.cost_castFunction]
  have h := framed_cost rep data cost primitive sizes laws dataLaws mono prepareExpression input W
    (SeedTape.NativeScan.scanTime overhead W remainingCap comparisonTime zeroTime +
      addTime + 1024 * overhead (256 * W))
    (hh.trans hw) (hu.trans hw) hin
    (by rw [prepareExpression_value]; exact hout.trans (by omega)) he
  exact h.trans (by dsimp only [prepareTime, W] at *; omega)

end Signatures.Runtime.Schnorr.RawTape.NativeUniform
