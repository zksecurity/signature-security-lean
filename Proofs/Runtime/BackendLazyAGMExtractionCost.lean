import Proofs.Runtime.BackendLazyAGMExtraction
import Proofs.Runtime.BackendExpressionCost
import Proofs.Runtime.BackendDataSize

/-! Costs of the extraction wrapper's actual local expressions. Complete
retained contexts, group/scalar zero creation, query keys, argument frames, and
final field arithmetic are charged from individual primitive contracts. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

/-- Exact final arithmetic syntax in `extractGood`. -/
def goodExtractResult : Expr CryptoOp
    [scalar, scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy] scalar :=
  .op .div (.pair (.op .add (.pair (.fst (.snd v4)) v2)) (.op .sub (.pair v0 v1)))

/-- Exact final arithmetic syntax in `extractBad`. -/
def badExtractResult : Expr CryptoOp
    [.pair scalar scalar, .pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy] scalar :=
  .op .div (.pair (.op .neg (.op .sub (.pair (.snd v0) (.snd v1))))
    (.op .sub (.pair (.fst v0) (.fst v1))))

def evaluateTokenArgs : Args CryptoOp
    [.list evalRowTy, .list (AGM.tokenTy message), .list scalar, evalRowTy]
    [.list evalRowTy, evalRowTy] := .cons v0 (.cons v3 .nil)

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include laws dataLaws primitiveBound sizes mono

theorem defaultRow_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [AGM.outputTy message, transcriptTy])
    (width zeroTime groupZeroTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hg : Q.size (rep.ty point₁) (0 : G₁) ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy message, transcriptTy]) env ≤ width)
    (hz : (primitiveBound CryptoOp.zero).time () ≤ zeroTime)
    (hgz : (primitiveBound CryptoOp.zero₁).time () ≤ groupZeroTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive defaultRow) env ≤
      zeroTime + groupZeroTime + 32 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [defaultRow, v0, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, DataCostLaws.unitBound,
    Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem goodExtractResult_cost
    (env : Env (cryptoBase F G₁ G₂ M M)
      [scalar, scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy])
    (width addTime subTime divTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [scalar, scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy]) env ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ha : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ addTime)
    (hs : ∀ x y : F, (primitiveBound CryptoOp.sub).time (x, y) ≤ subTime)
    (hd : ∀ x y : F, (primitiveBound CryptoOp.div).time (x, y) ≤ divTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive goodExtractResult) env ≤
      addTime + subTime + divTime + 64 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [goodExtractResult, v0, v1, v2, v4, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem badExtractResult_cost
    (env : Env (cryptoBase F G₁ G₂ M M)
      [.pair scalar scalar, .pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy])
    (width subTime negTime divTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [.pair scalar scalar, .pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy]) env ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (hs : ∀ x y : F, (primitiveBound CryptoOp.sub).time (x, y) ≤ subTime)
    (hn : ∀ x : F, (primitiveBound CryptoOp.neg).time x ≤ negTime)
    (hd : ∀ x y : F, (primitiveBound CryptoOp.div).time (x, y) ≤ divTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive badExtractResult) env ≤
      2 * subTime + negTime + divTime + 64 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [badExtractResult, v0, v1, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    Expr.denote, Var.get, arithmetic, LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem evaluateTokenArgs_cost
    (env : Env (cryptoBase F G₁ G₂ M M)
      [.list evalRowTy, .list (AGM.tokenTy message), .list scalar, evalRowTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [.list evalRowTy, .list (AGM.tokenTy message), .list scalar, evalRowTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive evaluateTokenArgs) env ≤
      16 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [evaluateTokenArgs, v0, v3, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.LazyAGM
