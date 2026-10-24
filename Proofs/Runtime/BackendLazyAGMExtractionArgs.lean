import Proofs.Runtime.BackendLazyAGMExtractionCost

/-! Native argument and final-target selection costs for both extraction
wrappers. Their full environments retain the output's coefficient lists and
both transcripts, including data unused by a particular extraction branch. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

def goodHashArgs : Args CryptoOp [evalRowTy, AGM.outputTy message, transcriptTy]
    [.list (AGM.tokenTy message), .list scalar, evalRowTy] :=
  .cons (.fst v2) (.cons (.fst (.snd (.snd v1))) (.cons v0 .nil))

def goodSignArgs : Args CryptoOp [scalar, evalRowTy, AGM.outputTy message, transcriptTy]
    [.list (AGM.tokenTy message), .list scalar, evalRowTy] :=
  .cons (.snd v3) (.cons (.snd (.snd (.snd v2))) (.cons v1 .nil))

def badSignArgs : Args CryptoOp [evalRowTy, AGM.outputTy message, transcriptTy]
    [.list (AGM.tokenTy message), .list scalar, evalRowTy] :=
  .cons (.snd v2) (.cons (.snd (.snd (.snd v1))) (.cons v0 .nil))

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

theorem goodHashArgs_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [evalRowTy, AGM.outputTy message, transcriptTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [evalRowTy, AGM.outputTy message, transcriptTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive goodHashArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [goodHashArgs, v0, v1, v2, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem goodSignArgs_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [scalar, evalRowTy, AGM.outputTy message, transcriptTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [scalar, evalRowTy, AGM.outputTy message, transcriptTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive goodSignArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [goodSignArgs, v0, v1, v2, v3, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem badSignArgs_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [evalRowTy, AGM.outputTy message, transcriptTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [evalRowTy, AGM.outputTy message, transcriptTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive badSignArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [badSignArgs, v0, v1, v2, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem goodTarget_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy])
    (width : Nat)
    (hi : Q.size (rep.env [scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy]) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (.fst v3 : Expr CryptoOp [scalar, scalar, evalRowTy, AGM.outputTy message, transcriptTy] message)) env ≤
      9 * overhead (16 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 16 * width, overhead k ≤ overhead (16 * width) := fun _ hk => mono hk
  dsimp only [v3, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.fst, LocalBound.snd, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem badTarget_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [.pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy])
    (width : Nat)
    (hi : Q.size (rep.env [.pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy]) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (.fst v2 : Expr CryptoOp [.pair scalar scalar, evalRowTy, AGM.outputTy message, transcriptTy] message)) env ≤
      7 * overhead (16 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 16 * width, overhead k ≤ overhead (16 * width) := fun _ hk => mono hk
  dsimp only [v2, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.fst, LocalBound.snd, Expr.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.LazyAGM
