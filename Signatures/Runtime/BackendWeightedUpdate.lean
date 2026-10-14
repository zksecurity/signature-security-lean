import Signatures.Runtime.BackendExpressionCost
import Signatures.Runtime.BackendDataSize
import Signatures.Runtime.WeightedEvaluate

/-! Actual compiled accumulator-update costs. Natural-counter increments,
field multiplication/addition, retained contexts, and pair construction are
charged from their primitive and structural contracts. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Evaluate

open BackendProgram LazyAGM.ReplySyntax

variable {indexTy : Ty CryptoAtom}

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
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include sizes mono

theorem goodUpdate_time_bound
    (answer acc : F) (row : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) (n : Nat)
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (width natTime addTime mulTime : Nat)
    (hh : header ≤ width)
    (hi : Q.size (rep.env [scalar, (evalRowTy indexTy), evalStateTy scalar, .list (evalRowTy indexTy), (evalRowTy indexTy)])
      (answer, row, (n, acc), rows, default, ()) ≤ width)
    (h1 : Q.size rep.data.nat 1 ≤ width)
    (hn : Q.size rep.data.nat (n + 1) ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : (primitiveBound CryptoOp.natAdd).time (n, 1) ≤ natTime)
    (ha : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ addTime)
    (hm : ∀ x y : F, (primitiveBound CryptoOp.mul).time (x, y) ≤ mulTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (evalUpdate goodCombine)).time (answer, row, (n, acc), rows, default, ()) ≤
        natTime + addTime + mulTime + 128 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  simp only [evalUpdate, goodCombine, v0, v1, v2, Expr.weakenTail, Var.weakenTail]
  dsimp only [List.append, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.natBound, DataCostLaws.unitBound, Expr.denote, Var.get, arithmetic,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

theorem badUpdate_time_bound
    (answer acc : F × F) (row : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) (n : Nat)
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (width natTime addTime mulTime : Nat)
    (hh : header ≤ width)
    (hi : Q.size (rep.env [.pair scalar scalar, (evalRowTy indexTy),
        evalStateTy (.pair scalar scalar), .list (evalRowTy indexTy), (evalRowTy indexTy)])
      (answer, row, (n, acc), rows, default, ()) ≤ width)
    (h1 : Q.size rep.data.nat 1 ≤ width)
    (hn : Q.size rep.data.nat (n + 1) ≤ width)
    (hf : ∀ f : F, Q.size (rep.ty scalar) f ≤ width)
    (ht : (primitiveBound CryptoOp.natAdd).time (n, 1) ≤ natTime)
    (ha : ∀ x y : F, (primitiveBound CryptoOp.add).time (x, y) ≤ addTime)
    (hm : ∀ x y : F, (primitiveBound CryptoOp.mul).time (x, y) ≤ mulTime) :
    (Expression.compileBound rep data (arithmetic F G₁ G₂ K M cost) primitive laws dataLaws
      primitiveBound (evalUpdate badCombine)).time (answer, row, (n, acc), rows, default, ()) ≤
        natTime + 2 * addTime + 2 * mulTime + 192 * overhead (128 * width) := by
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  simp only [evalUpdate, badCombine, v0, v1, v2, Expr.weakenTail, Var.weakenTail]
  dsimp only [List.append, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
    DataCostLaws.natBound, DataCostLaws.unitBound, Expr.denote, Var.get, arithmetic,
    LanguageRepresentation.ty, LanguageRepresentation.env] at *
  grind only

end Signatures.Runtime.WeightedAGM.Evaluate
