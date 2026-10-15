import Signatures.Runtime.BackendSchnorrRawReset
import Signatures.Runtime.BackendSchnorrRawUniformLocalCost
import Signatures.Runtime.BackendSeedTapeResetCost

/-! Native reset runtime, including trimming, reversal, retained input, and
construction of both output lists. All costs follow from primitive operations
and backend data/representation laws. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.RawTape.NativeReset

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

private abbrev v0 {a Γ} : Expr CryptoOp (a :: Γ) a := .var .here
private abbrev v1 {a b Γ} : Expr CryptoOp (a :: b :: Γ) b := .var (.there .here)
private abbrev v2 {a b c Γ} : Expr CryptoOp (a :: b :: c :: Γ) c := .var (.there (.there .here))

private def resetWith
    (reset : Expr CryptoOp [.nat, .nat, .list Replay.Mixed.event, Replay.Mixed.event, inputTy]
      (.list Replay.Mixed.event)) : Expr CryptoOp [inputTy] stateTy :=
  .letE (.pair (.nat 1) (.pair (.fst (.snd v0)) (.nat 0)))
    (.letE (.fst (.snd (.snd v1)))
      (.letE (.fst v2)
        (.letE (.nat 1)
          (.letE reset (.pair v0 v0)))))

include sizes mono

private theorem resetWith_time
    (reset : Expr CryptoOp [.nat, .nat, .list Replay.Mixed.event, Replay.Mixed.event, inputTy]
      (.list Replay.Mixed.event))
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M)) (width resetTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hi : Q.size (rep.ty inputTy) input ≤ width)
    (ho : Q.size (rep.ty (.list Replay.Mixed.event))
      (reset.denote (arithmetic F G₁ G₂ K M cost)
        (1, input.1, input.2.2.1, (1, input.2.1, 0), input, ())) ≤ width)
    (ht : (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound reset).time (1, input.1, input.2.2.1, (1, input.2.1, 0), input, ()) ≤ resetTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (resetWith reset)).time (input, ()) ≤ resetTime + 512 * overhead (256 * width) := by
  have hp := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  dsimp only [resetWith, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.natBound, DataCostLaws.unitBound, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env,
    id, Function.comp_def] at *
  grind only

def frameWidth (width savedCap remainingCap : Nat) : Nat :=
  (12 * (savedCap + remainingCap) + 32) * width

def localTime (overhead : Nat → Nat) (width savedCap remainingCap comparisonTime subtractTime : Nat) : Nat :=
  let W := frameWidth width savedCap remainingCap
  SeedTape.NativeReset.resetTime overhead W savedCap comparisonTime subtractTime +
    516 * overhead (256 * W)

include lists laws dataLaws

theorem compiled_cost (width savedCap remainingCap slotCap comparisonTime subtractTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (hn0 : Q.size rep.data.nat 0 ≤ width) (hn1 : Q.size rep.data.nat 1 ≤ width)
    (hn : ∀ n ≤ slotCap, Q.size rep.data.nat n ≤ width)
    (hcompare : ∀ n m, Q.size rep.data.nat n ≤ width → Q.size rep.data.nat m ≤ width →
      (primitiveBound .natEq).time (n, m) ≤ comparisonTime)
    (hsub : ∀ n ≤ slotCap, (primitiveBound .natSub).time (n, 1) ≤ subtractTime)
    (input : inputTy.Value (cryptoBase F G₁ G₂ K M))
    (bound : InputBound (Q := Q) rep width savedCap remainingCap slotCap input) :
    Q.cost (compiled rep data cost primitive) input ≤
      localTime overhead width savedCap remainingCap comparisonTime subtractTime := by
  let W := frameWidth width savedCap remainingCap
  have hw : width ≤ W := by dsimp [W, frameWidth]; nlinarith
  have hin : Q.size (rep.ty inputTy) input ≤ W :=
    (input_size rep sizes lists width savedCap remainingCap slotCap hh hn input bound).trans
      (by dsimp [W, frameWidth]; nlinarith)
  have result := property rep width savedCap remainingCap slotCap hn0 hn1 input bound
  have hout : Q.size (rep.ty stateTy) (value input) ≤ W :=
    (output_size rep sizes lists width savedCap remainingCap slotCap hh hn0 hn1 input bound).trans
      (by dsimp [W, frameWidth]; nlinarith)
  have htape : Q.size (rep.ty (.list Replay.Mixed.event))
      (SeedTape.reset 1 input.1 (1, input.2.1, 0) input.2.2.1) ≤ W :=
    (NativeUniform.tape_size rep sizes lists width (savedCap + 1) hh _ result.1).trans
      (by dsimp [W, frameWidth]; nlinarith)
  have hcell := NativeUniform.cell_size rep sizes width hh (1, input.2.1, 0)
    ⟨hn1, bound.2.1, hn0⟩
  have hi := input_size rep sizes lists width savedCap remainingCap slotCap hh hn input bound
  have hp := @sizes.prod_le
  have henv : Q.size (rep.env [Replay.Mixed.event, inputTy]) ((1, input.2.1, 0), input, ()) ≤ W := by
    dsimp only [LanguageRepresentation.env, W, frameWidth] at *
    grind only
  have resetValue := (Expr.weakenTail_denote (Δ := [inputTy]) (arithmetic F G₁ G₂ K M cost)
    SeedTape.resetCode (1, input.1, input.2.2.1, (1, input.2.1, 0), ()) (input, ())).trans
      (SeedTape.resetCode_denote cost 1 input.1 input.2.2.1 (1, input.2.1, 0))
  simp only [Env.append] at resetValue
  have ht := SeedTape.NativeReset.reset_time (Γ := [inputTy])
    rep data cost primitive laws dataLaws primitiveBound sizes lists mono
    1 input.1 input.2.2.1 (1, input.2.1, 0) (input, ()) W savedCap slotCap comparisonTime subtractTime
    (hh.trans hw) (hu.trans hw) (fun b => (hb b).trans hw) (hn0.trans hw) (hn1.trans hw)
    (fun n hn' => (hn n hn').trans hw) bound.1 (hn1.trans hw) henv
    (fun x member => (NativeUniform.cell_size rep sizes width hh x (bound.2.2.1.1 x member)).trans
      (by dsimp [W, frameWidth]; nlinarith)) bound.2.2.1.2
    (fun x member => hcompare x.1 1 (bound.2.2.1.1 x member).1 hn1)
    (fun n hn' => hcompare n 0 (hn n hn') hn0) hsub
  have hs := resetWith_time rep data cost primitive sizes laws dataLaws primitiveBound mono
    (SeedTape.resetCode.weakenTail [inputTy]) input W
    (SeedTape.NativeReset.resetTime overhead W savedCap comparisonTime subtractTime)
    (hh.trans hw) (hu.trans hw) (hn0.trans hw) (hn1.trans hw) hin (by rw [resetValue]; exact htape) ht
  have he : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive expression)
      (input, ()) ≤ SeedTape.NativeReset.resetTime overhead W savedCap comparisonTime subtractTime +
        512 * overhead (256 * W) :=
    (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound expression (input, ())).trans hs
  rw [compiled, QuantitativeStepClass.Realizer.cost_castFunction]
  exact (NativeUniform.framed_cost rep data cost primitive sizes laws dataLaws mono expression input W
    (SeedTape.NativeReset.resetTime overhead W savedCap comparisonTime subtractTime + 512 * overhead (256 * W))
    (hh.trans hw) (hu.trans hw) hin (by rw [expression_value]; omega) he).trans
      (by dsimp only [localTime, W]; omega)

end Signatures.Runtime.Schnorr.RawTape.NativeReset
