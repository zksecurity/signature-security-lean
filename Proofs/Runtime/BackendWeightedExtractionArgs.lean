import Proofs.Runtime.BackendWeightedExtractionCost
import Proofs.Runtime.BackendWeightedSignInputs

/-! Native argument and final-target selection costs for both extraction
wrappers. Their full environments retain the output's coefficient lists and
both transcripts, including data unused by a particular extraction branch. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate LazyAGM.ReplySyntax

variable {indexTy messageTy : Ty CryptoAtom}

def goodHashArgs : Args CryptoOp [(evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]
    [.list (AGM.tokenTy indexTy), .list scalar, (evalRowTy indexTy)] :=
  .cons (.fst v2) (.cons (.fst (.snd (.snd v1))) (.cons v0 .nil))

def goodSignArgs : Args CryptoOp [scalar, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]
    [.list (AGM.tokenTy messageTy), .list scalar, (evalRowTy indexTy)] :=
  .cons (.snd v3) (.cons (.snd (.snd (.snd v2))) (.cons v1 .nil))

def badSignArgs : Args CryptoOp [(evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]
    [.list (AGM.tokenTy messageTy), .list scalar, (evalRowTy indexTy)] :=
  .cons (.snd v2) (.cons (.snd (.snd (.snd v1))) (.cons v0 .nil))

def goodTargetArgs : Args CryptoOp
    [scalar, scalar, evalRowTy indexTy, AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy]
    [messageTy, evalRowTy indexTy] := .cons (.fst v3) (.cons v2 .nil)

def badTargetArgs : Args CryptoOp
    [.pair scalar scalar, evalRowTy indexTy, AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy]
    [messageTy, evalRowTy indexTy] := .cons (.fst v2) (.cons v1 .nil)

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

theorem goodHashArgs_cost
    (env : Env (cryptoBase F G₁ G₂ K M) [(evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [(evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive goodHashArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
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
    (env : Env (cryptoBase F G₁ G₂ K M) [scalar, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [scalar, (evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive goodSignArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
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
    (env : Env (cryptoBase F G₁ G₂ K M) [(evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [(evalRowTy indexTy), AGM.outputTy messageTy, (Reply.transcriptTy indexTy messageTy)]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive badSignArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
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

theorem goodTargetArgs_cost
    (env : Env (cryptoBase F G₁ G₂ K M) [scalar, scalar, evalRowTy indexTy, AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [scalar, scalar, evalRowTy indexTy, AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive goodTargetArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [goodTargetArgs, v2, v3, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem badTargetArgs_cost
    (env : Env (cryptoBase F G₁ G₂ K M) [.pair scalar scalar, evalRowTy indexTy, AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy])
    (width : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [.pair scalar scalar, evalRowTy indexTy, AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy]) env ≤ width) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive badTargetArgs) env ≤
      64 * overhead (128 * width) := by
  apply (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [badTargetArgs, v1, v2, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst,
    LocalBound.snd, DataCostLaws.unitBound, Expr.denote, Args.denote, Var.get,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem defaultRow_cost (index : Index)
    (env : Env (cryptoBase F G₁ G₂ K M) [AGM.outputTy index.messageTy, Reply.transcriptTy index.ty index.messageTy])
    (width finZeroTime zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [AGM.outputTy index.messageTy, Reply.transcriptTy index.ty index.messageTy]) env ≤ width)
    (hf : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hj : Q.size (rep.ty (boundedNat index.bound)) (0 : Fin (index.bound + 1)) ≤ width)
    (hfin : (primitiveBound (.finZero index.bound)).time () ≤ finZeroTime)
    (hzero : (primitiveBound .zero).time () ≤ zeroTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (defaultRow index.defaultTerm)) env ≤ finZeroTime + zeroTime + 64 * overhead (128 * width) := by
  apply (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
    primitiveBound _ _).trans
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  cases index <;>
    dsimp only [defaultRow, Index.defaultTerm, Index.messageTy, Index.ty, Index.bound,
      Reply.oopsDefault, Reply.proximityDefault, Reply.syncDefault, Expr.weakenTail, Var.weakenTail,
      v0, Expression.compileBound, Expression.variableBound, LocalBound.compose,
      LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity, DataCostLaws.unitBound,
      Expr.denote, Var.get, arithmetic, Terms.termTy, Weights.oopsKey, Weights.oopsMessage,
      Weights.proximityKey, Weights.proximityTupleMessage, Weights.syncMessage, LanguageRepresentation.ty,
      LanguageRepresentation.env, List.cons_append, List.nil_append, List.append] at * <;>
    grind only

end Signatures.Runtime.WeightedAGM.Extract
