import Proofs.Runtime.BackendSchnorrROMExtractionComponentBudget

/-! Costs of both extraction folds on the actual empty/singleton pass outputs.
Each fold charges its seed, retained environment and traversal controls. -/

open PFunctor

namespace Signatures.Runtime.Schnorr.ListROM.NativeExtraction

open BackendProgram

def innerWith (step : Expr CryptoOp (bodyTypes [resultTy, inputTy]) resultTy) :
    Expr CryptoOp [cachePassOutput, resultTy, inputTy] resultTy :=
  .fold (.snd (.var (.there (.there .here)))) (.pair (.bool false) (.op .zero .unit)) step

def outerWith (step : Expr CryptoOp [cachePassOutput, resultTy, inputTy] resultTy) :
    Expr CryptoOp [inputTy] resultTy :=
  .fold (.fst (.var .here)) (.pair (.bool false) (.op .zero .unit)) step

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

include sizes lists mono

theorem innerWith_time (step : Expr CryptoOp (bodyTypes [resultTy, inputTy]) resultTy)
    (first : cachePassOutput.Value (cryptoBase F G₁ G₂ K M)) (acc : Bool × F)
    (xs ys : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) (width bodyTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.env [cachePassOutput, resultTy, inputTy]) (first, acc, (xs, ys), ()) ≤ width)
    (hlen : ys.length ≤ 1) (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (ho : ∀ p ∈ ys, Q.size (rep.ty resultTy)
      (step.denote (arithmetic F G₁ G₂ K M cost) (p, (false, 0), first, acc, (xs, ys), ())) ≤ width)
    (hc : ∀ p ∈ ys, (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      step).time (p, (false, 0), first, acc, (xs, ys), ()) ≤ bodyTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (innerWith step)).time (first, acc, (xs, ys), ()) ≤ zeroTime + bodyTime + 128 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := lists.nil_le (rep.ty cachePassOutput)
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  cases ys with
  | nil =>
      dsimp only [innerWith, Expression.compileBound, Expression.variableBound,
        LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
        DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound,
        foldWork, foldFee, List.foldl_nil, Expr.denote, Var.get, arithmetic, id,
        LanguageRepresentation.env, LanguageRepresentation.ty] at *
      grind only
  | cons p ps =>
      have ht : ps = [] := by simpa using hlen
      subst ps
      have hout := ho p (by simp)
      have hbody := hc p (by simp)
      clear ho hc
      dsimp only [innerWith, Expression.compileBound, Expression.variableBound,
        LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
        DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound,
        foldWork, foldFee, List.foldl_cons, List.foldl_nil, Expr.denote, Var.get, arithmetic, id,
        LanguageRepresentation.env, LanguageRepresentation.ty] at *
      grind only

theorem outerWith_time (step : Expr CryptoOp [cachePassOutput, resultTy, inputTy] resultTy)
    (xs ys : NativePass.outputTy.Value (cryptoBase F G₁ G₂ K M)) (width bodyTime zeroTime : Nat)
    (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width) (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.ty inputTy) (xs, ys) ≤ width)
    (hlen : xs.length ≤ 1) (hzero : (primitiveBound .zero).time () ≤ zeroTime)
    (ho : ∀ p ∈ xs, Q.size (rep.ty resultTy)
      (step.denote (arithmetic F G₁ G₂ K M cost) (p, (false, 0), (xs, ys), ())) ≤ width)
    (hc : ∀ p ∈ xs, (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      step).time (p, (false, 0), (xs, ys), ()) ≤ bodyTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws primitiveBound
      (outerWith step)).time ((xs, ys), ()) ≤ zeroTime + bodyTime + 128 * overhead (256 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hnil := lists.nil_le (rep.ty cachePassOutput)
  have hfee : ∀ n ≤ 256 * width, overhead n ≤ overhead (256 * width) := fun _ hn => mono hn
  cases xs with
  | nil =>
      dsimp only [outerWith, Expression.compileBound, Expression.variableBound,
        LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
        DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound,
        foldWork, foldFee, List.foldl_nil, Expr.denote, Var.get, arithmetic, id,
        LanguageRepresentation.env, LanguageRepresentation.ty] at *
      grind only
  | cons p ps =>
      have ht : ps = [] := by simpa using hlen
      subst ps
      have hout := ho p (by simp)
      have hbody := hc p (by simp)
      clear ho hc
      dsimp only [outerWith, Expression.compileBound, Expression.variableBound,
        LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
        DataCostLaws.foldBound, DataCostLaws.unitBound, DataCostLaws.boolBound,
        foldWork, foldFee, List.foldl_cons, List.foldl_nil, Expr.denote, Var.get, arithmetic, id,
        LanguageRepresentation.env, LanguageRepresentation.ty] at *
      grind only

end Signatures.Runtime.Schnorr.ListROM.NativeExtraction
