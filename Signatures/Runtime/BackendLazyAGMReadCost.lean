import Signatures.Runtime.BackendLazyAGMRead
import Signatures.Runtime.BackendExpressionCost
import Signatures.Runtime.BackendDataSize

/-! Derived costs of the private extraction-read argument frames. The
fallback construction is executed even on hits, and is charged here. -/

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
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include laws dataLaws primitiveBound sizes mono

theorem goodReadArgs_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [message, cacheTy scalar])
    (width zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.env [message, cacheTy scalar]) env ≤ width)
    (ht : (primitiveBound CryptoOp.zero).time () ≤ zeroTime) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (readArgs (.op .zero .unit))) env ≤ zeroTime + 32 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive laws
    dataLaws primitiveBound (readArgs (.op .zero .unit)) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [readArgs, v0, v1, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env,
    Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

theorem badReadArgs_cost
    (env : Env (cryptoBase F G₁ G₂ M M) [message, cacheTy (.pair scalar scalar)])
    (width zeroTime : Nat) (hh : header ≤ width) (hu : Q.size rep.data.unit () ≤ width)
    (hz : Q.size (rep.ty scalar) (0 : F) ≤ width)
    (hi : Q.size (rep.env [message, cacheTy (.pair scalar scalar)]) env ≤ width)
    (ht : (primitiveBound CryptoOp.zero).time () ≤ zeroTime) :
    Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ M M cost) primitive
      (readArgs (.pair (.op .zero .unit) (.op .zero .unit)))) env ≤
        2 * zeroTime + 40 * overhead (32 * width) := by
  refine (Expression.cost_arguments_le rep data (arithmetic F G₁ G₂ M M cost) primitive laws
    dataLaws primitiveBound (readArgs (.pair (.op .zero .unit) (.op .zero .unit))) env).trans ?_
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [readArgs, v0, v1, Expression.argumentsBound, Expression.compileBound,
    Expression.variableBound, LocalBound.compose, LocalBound.pair, LocalBound.fst, LocalBound.snd,
    DataCostLaws.unitBound, LanguageRepresentation.ty, LanguageRepresentation.env,
    Expr.denote, Args.denote, Var.get, arithmetic] at *
  grind only

end Signatures.Runtime.LazyAGM
