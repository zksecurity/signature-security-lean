import Proofs.Runtime.BackendLazyAGMReply
import Proofs.Runtime.BackendExpressionCost
import Proofs.Runtime.BackendDataSize

/-! Local costs of the implemented lazy AGM reply expressions. Every bound is
derived from individual primitive and structural certificates. In particular,
transcript construction and retained argument frames are charged. -/

open PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

include laws dataLaws primitiveBound sizes mono

theorem goodCacheArgs_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [message, storeTy scalar goodConfigTy])
    (width zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.env [message, storeTy scalar goodConfigTy]) env ≤ width)
    (ht : (primitiveBound CryptoOp.zero).time () ≤ zeroTime) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (cacheArgs (.op .zero .unit))) env ≤ zeroTime + 32 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive laws
    dataLaws primitiveBound (cacheArgs (.op .zero .unit)) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [cacheArgs, v0, v1, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env,
    Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

theorem badCacheArgs_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [message, storeTy (.pair scalar scalar) badConfigTy])
    (width zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.env [message, storeTy (.pair scalar scalar) badConfigTy]) env ≤ width)
    (ht : (primitiveBound CryptoOp.zero).time () ≤ zeroTime) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (cacheArgs (.pair (.op .zero .unit) (.op .zero .unit)))) env ≤
        2 * zeroTime + 40 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive laws
    dataLaws primitiveBound (cacheArgs (.pair (.op .zero .unit) (.op .zero .unit))) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [cacheArgs, v0, v1, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env,
    Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

include lists in
theorem goodReplyResult_cost (signing : Bool)
    (env : Env (cryptoBase F G₁ G₂ M M) [cacheResultTy scalar, message, storeTy scalar goodConfigTy])
    (width scaleTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [cacheResultTy scalar, message, storeTy scalar goodConfigTy]) env ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (ht : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ scaleTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (replyResult signing (goodResponse signing))) env ≤ scaleTime + 192 * overhead (64 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive laws
    dataLaws primitiveBound (replyResult signing (goodResponse signing)) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ hn => mono hn
  cases signing <;>
    simp only [replyResult, goodResponse, v0, v1, v2, v3, v4, v5,
      Expr.weakenTail, Var.weakenTail] <;>
    dsimp only [List.append, Expr.weakenTail, Var.weakenTail, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.consBound, LanguageRepresentation.ty, LanguageRepresentation.env,
      Expr.denote, Var.get, arithmetic, Bool.false_eq_true, ite_false, ite_true] at * <;>
    grind only

include lists in
theorem badReplyResult_cost (signing : Bool)
    (env : Env (cryptoBase F G₁ G₂ M M)
      [cacheResultTy (.pair scalar scalar), message, storeTy (.pair scalar scalar) badConfigTy])
    (width scaleTime addTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env
      [cacheResultTy (.pair scalar scalar), message, storeTy (.pair scalar scalar) badConfigTy]) env ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (ht : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ scaleTime)
    (ha : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ addTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (replyResult signing (badResponse signing))) env ≤
        3 * scaleTime + addTime + 256 * overhead (64 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive laws
    dataLaws primitiveBound (replyResult signing (badResponse signing)) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ hn => mono hn
  cases signing <;>
    simp only [replyResult, badResponse, v0, v1, v2, v3, v4, v5,
      Expr.weakenTail, Var.weakenTail] <;>
    dsimp only [List.append, Expr.weakenTail, Var.weakenTail, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.consBound, LanguageRepresentation.ty, LanguageRepresentation.env,
      Expr.denote, Var.get, arithmetic, Bool.false_eq_true, ite_false, ite_true] at * <;>
    grind only

end Signatures.Runtime.LazyAGM
