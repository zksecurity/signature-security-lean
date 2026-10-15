import Signatures.Runtime.WeightedExtraction
import Signatures.Runtime.BackendExpressionCost
import Signatures.Runtime.BackendDataSize

/-! Actual local extraction costs, including argument construction and final
field arithmetic in the full retained context. Index and message types remain
independent. Component assembly charges native calls and state retention. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate LazyAGM.ReplySyntax

variable {indexTy messageTy : Ty CryptoAtom}

def goodResult : Expr CryptoOp
    [scalar, scalar, scalar, evalRowTy indexTy, AGM.outputTy messageTy,
      Reply.transcriptTy indexTy messageTy] scalar :=
  .op .div (.pair (.op .add (.pair (.fst (.snd v4)) v2)) (.op .sub (.pair v0 v1)))

def badResult : Expr CryptoOp
    [.pair scalar scalar, .pair scalar scalar, evalRowTy indexTy, AGM.outputTy messageTy,
      Reply.transcriptTy indexTy messageTy] scalar :=
  .op .div (.pair (.op .neg (.op .sub (.pair (.snd v0) (.snd v1))))
    (.op .sub (.pair (.fst v0) (.fst v1))))

def coefficientPrepareArgs : Args CryptoOp
    [.list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy]
    [.list (AGM.tokenTy messageTy), .list scalar] := .cons v0 (.cons v1 .nil)

def coefficientEvaluateArgs : Args CryptoOp
    [.list (evalRowTy indexTy), .list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy]
    [.list (evalRowTy indexTy), evalRowTy indexTy] := .cons v0 (.cons v3 .nil)

def targetPrepareArgs : Args CryptoOp
    [messageTy, evalRowTy indexTy]
    [messageTy] := .cons v0 .nil

def targetEvaluateArgs : Args CryptoOp
    [.list (evalRowTy indexTy), messageTy, evalRowTy indexTy]
    [.list (evalRowTy indexTy), evalRowTy indexTy] := .cons v0 (.cons v2 .nil)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include laws dataLaws primitiveBound sizes mono

theorem goodResult_cost
    (env : Env (cryptoBase F G₁ G₂ K M)
      [scalar, scalar, scalar, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)])
    (width addTime subTime divTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [scalar, scalar, scalar, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) env ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ha : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ addTime)
    (hs : ∀ x y : F, (primitiveBound CryptoOp.sub).time (x, y) ≤ subTime)
    (hd : ∀ x y : F, (primitiveBound CryptoOp.div).time (x, y) ≤ divTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive goodResult) env ≤
      addTime + subTime + divTime + 64 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [goodResult, v0, v1, v2, v4, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem badResult_cost
    (env : Env (cryptoBase F G₁ G₂ K M)
      [.pair scalar scalar, .pair scalar scalar, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)])
    (width subTime negTime divTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [.pair scalar scalar, .pair scalar scalar, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) env ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hs : ∀ x y : F, (primitiveBound CryptoOp.sub).time (x, y) ≤ subTime)
    (hn : ∀ x : F, (primitiveBound CryptoOp.neg).time x ≤ negTime)
    (hd : ∀ x y : F, (primitiveBound CryptoOp.div).time (x, y) ≤ divTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive badResult) env ≤
      2 * subTime + negTime + divTime + 64 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [badResult, v0, v1, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem coefficientPrepareArgs_cost
    (env : Env (cryptoBase F G₁ G₂ K M) [.list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [.list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive coefficientPrepareArgs) env ≤
      16 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [coefficientPrepareArgs, v0, v1, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem coefficientEvaluateArgs_cost
    (env : Env (cryptoBase F G₁ G₂ K M) [.list (evalRowTy indexTy), .list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [.list (evalRowTy indexTy), .list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive coefficientEvaluateArgs) env ≤
      16 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [coefficientEvaluateArgs, v0, v3, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem targetPrepareArgs_cost
    (env : Env (cryptoBase F G₁ G₂ K M) [messageTy, evalRowTy indexTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [messageTy, evalRowTy indexTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive targetPrepareArgs) env ≤
      16 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [targetPrepareArgs, v0, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem targetEvaluateArgs_cost
    (env : Env (cryptoBase F G₁ G₂ K M) [.list (evalRowTy indexTy), messageTy, evalRowTy indexTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [.list (evalRowTy indexTy), messageTy, evalRowTy indexTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive targetEvaluateArgs) env ≤
      16 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [targetEvaluateArgs, v0, v2, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.WeightedAGM.Extract
