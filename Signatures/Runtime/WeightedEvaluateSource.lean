import Signatures.Runtime.WeightedEvaluate

/-! The bounded left-accumulating evaluator has exactly the source game's
ordered cache-query computation. Equality holds in any effect monad, preserving
the cache state as well as the extracted value under stateful interpretation. -/

open OracleComp OracleSpec Model.LazyAGM

namespace Signatures.Runtime.WeightedAGM.Evaluate

variable {F R M : Type} [AddCommMonoid R] [SMul F R]
  {N : Type → Type} [Monad N] [LawfulMonad N]

theorem foldTerms_simulate (impl : QueryImpl (baseSpec M R) N)
    (rows : List (M × F)) (acc : R) :
    rows.foldlM (fun acc row => do
      let answer : R ← impl (.inr row.1)
      pure (acc + row.2 • answer)) acc =
      (fun value => acc + value) <$> simulateQ impl (evalTerms rows) := by
  induction rows generalizing acc with
  | nil => simp [evalTerms]
  | cons row rows ih =>
      simp only [List.foldlM_cons, evalTerms, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, bind_assoc, pure_bind, map_bind]
      congr 1
      funext answer
      rw [ih]
      simp only [map_pure, bind_pure_comp]
      congr 1
      funext value
      exact add_assoc acc (row.2 • answer) value

variable {G₁ G₂ K L : Type} {indexTy : Ty CryptoAtom} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq L]
  (cost : PrimitiveCosts)

theorem evaluateRows_source {value : Ty CryptoAtom}
    [AddCommMonoid (value.Value (cryptoBase F G₁ G₂ K L))]
    [SMul F (value.Value (cryptoBase F G₁ G₂ K L))]
    (impl : QueryImpl (baseSpec (indexTy.Value (cryptoBase F G₁ G₂ K L)) (value.Value (cryptoBase F G₁ G₂ K L))) N)
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), (evalRowTy indexTy)] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K L) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K L) × F)
    (hz : zero.denote (arithmetic F G₁ G₂ K L cost) (rows, default, ()) = 0)
    (hc : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ K L cost) (answer, coeff, acc, ()) =
      acc + coeff • answer) :
    (evaluateRows zero combine).denote (arithmetic F G₁ G₂ K L cost)
      (evalSemantics (fun m => impl (.inr m))) (rows, default, ()) =
      simulateQ impl (evalTerms rows) := by
  rw [evaluateRows_denote, hz]
  simp_rw [hc]
  simpa only [zero_add, id_map'] using
    (foldTerms_simulate (F := F) (R := value.Value (cryptoBase F G₁ G₂ K L)) impl rows 0)

theorem evaluateGood_source (impl : QueryImpl (baseSpec (indexTy.Value (cryptoBase F G₁ G₂ K L)) F) N)
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K L) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K L) × F) :
    evaluateGood.denote (arithmetic F G₁ G₂ K L cost) (evalSemantics (fun m => impl (.inr m)))
      (rows, default, ()) =
      simulateQ impl (evalTerms rows) := by
  exact evaluateRows_source cost impl (.op .zero .unit) goodCombine rows default rfl
    (fun answer coeff acc => goodCombine_denote (G₁ := G₁) (G₂ := G₂) (K := K) (M := L) cost answer coeff acc)

theorem evaluateBad_source (impl : QueryImpl (baseSpec (indexTy.Value (cryptoBase F G₁ G₂ K L)) (F × F)) N)
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K L) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K L) × F) :
    evaluateBad.denote (arithmetic F G₁ G₂ K L cost) (evalSemantics (fun m => impl (.inr m)))
      (rows, default, ()) =
      simulateQ impl (evalTerms rows) := by
  exact evaluateRows_source cost impl (.pair (.op .zero .unit) (.op .zero .unit)) badCombine rows default rfl
    (fun answer coeff acc => badCombine_denote (G₁ := G₁) (G₂ := G₂) (K := K) (M := L) cost answer acc coeff)

end Signatures.Runtime.WeightedAGM.Evaluate
