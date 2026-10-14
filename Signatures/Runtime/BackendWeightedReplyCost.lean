import Signatures.Runtime.BackendWeightedReply
import Signatures.Runtime.BackendExpressionCost
import Signatures.Runtime.BackendDataSize

/-! Local costs of the implemented lazy AGM reply expressions. Every bound is
derived from individual primitive and structural certificates. In particular,
transcript construction and retained argument frames are charged. -/

open PFunctor

namespace Signatures.Runtime.WeightedAGM.Reply

open BackendProgram LazyAGM.ReplySyntax

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
  {header : Nat} (sizes : SizeLaws Q header) (lists : ListSizeLaws Q rep.data header)
  (mono : Monotone overhead)

variable {indexTy messageTy : Ty CryptoAtom}

include laws dataLaws primitiveBound sizes mono

theorem cacheArgs_cost {value config : Ty CryptoAtom} (signing : Bool)
    (env : Env (cryptoBase F G₁ G₂ K M)
      [requestTy indexTy messageTy signing, storeTy indexTy messageTy value config])
    (width : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [requestTy indexTy messageTy signing,
      storeTy indexTy messageTy value config]) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (cacheArgs signing)) env ≤ 16 * overhead (32 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound (cacheArgs signing) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [cacheArgs, v0, v1, Expression.compileBound, Expression.variableBound,
    LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    LanguageRepresentation.ty, LanguageRepresentation.env, Expr.denote, Var.get] at *
  grind only

include lists in
theorem goodReplyResult_cost (signing : Bool)
    (env : Env (cryptoBase F G₁ G₂ K M) [cacheResultTy indexTy scalar, requestTy indexTy messageTy signing, storeTy indexTy messageTy scalar LazyAGM.goodConfigTy])
    (width scaleTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [cacheResultTy indexTy scalar, requestTy indexTy messageTy signing, storeTy indexTy messageTy scalar LazyAGM.goodConfigTy]) env ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (ht : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ scaleTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (replyResult signing (LazyAGM.goodResponse signing))) env ≤ scaleTime + 192 * overhead (64 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound (replyResult signing (LazyAGM.goodResponse signing)) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ hn => mono hn
  cases signing <;>
    simp only [replyResult, LazyAGM.goodResponse, v0, v1, v2, v3, v4, v5,
      Expr.weakenTail, Var.weakenTail] <;>
    dsimp only [List.append, Expr.weakenTail, Var.weakenTail, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.consBound, LanguageRepresentation.ty, LanguageRepresentation.env,
      Expr.denote, Var.get, arithmetic, Bool.false_eq_true, ite_false, ite_true] at * <;>
    grind only

include lists in
theorem badReplyResult_cost (signing : Bool)
    (env : Env (cryptoBase F G₁ G₂ K M)
      [cacheResultTy indexTy (.pair scalar scalar), requestTy indexTy messageTy signing, storeTy indexTy messageTy (.pair scalar scalar) LazyAGM.badConfigTy])
    (width scaleTime addTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env
      [cacheResultTy indexTy (.pair scalar scalar), requestTy indexTy messageTy signing, storeTy indexTy messageTy (.pair scalar scalar) LazyAGM.badConfigTy]) env ≤ width)
    (hg : ∀ g : G₁, Q.size (rep.ty point₁) g ≤ width)
    (ht : ∀ rho : F, ∀ g : G₁, (primitiveBound CryptoOp.scale₁).time (rho, g) ≤ scaleTime)
    (ha : ∀ g h : G₁, (primitiveBound CryptoOp.add₁).time (g, h) ≤ addTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (replyResult signing (LazyAGM.badResponse signing))) env ≤
        3 * scaleTime + addTime + 256 * overhead (64 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive laws
    dataLaws primitiveBound (replyResult signing (LazyAGM.badResponse signing)) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hcons := @lists.cons_le
  have hfee : ∀ n ≤ 64 * width, overhead n ≤ overhead (64 * width) := fun _ hn => mono hn
  cases signing <;>
    simp only [replyResult, LazyAGM.badResponse, v0, v1, v2, v3, v4, v5,
      Expr.weakenTail, Var.weakenTail] <;>
    dsimp only [List.append, Expr.weakenTail, Var.weakenTail, Expression.compileBound, Expression.variableBound,
      LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd, LocalBound.identity,
      DataCostLaws.consBound, LanguageRepresentation.ty, LanguageRepresentation.env,
      Expr.denote, Var.get, arithmetic, Bool.false_eq_true, ite_false, ite_true] at * <;>
    grind only

end Signatures.Runtime.WeightedAGM.Reply
