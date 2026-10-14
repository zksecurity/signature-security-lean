import Signatures.Runtime.LazyAGMEvaluate

/-! The bounded left-accumulating evaluator has exactly the source game's
ordered cache-query computation. Equality holds in any effect monad, preserving
the cache state as well as the extracted value under stateful interpretation. -/

open OracleComp OracleSpec Model.LazyAGM

namespace Signatures.Runtime.LazyAGM

variable {F R M G : Type} [AddCommMonoid R] [SMul F R]
  {N : Type → Type} [Monad N] [LawfulMonad N]

theorem foldRows_simulate (impl : QueryImpl (baseSpec M R) N)
    (rows : List ((M × G) × F)) (acc : R) :
    rows.foldlM (fun acc row => do
      let answer : R ← impl (.inr row.1.1)
      pure (acc + row.2 • answer)) acc =
      (fun value => acc + value) <$> simulateQ impl (evalTerms (rows.map (fun row => (row.1.1, row.2)))) := by
  induction rows generalizing acc with
  | nil => simp [evalTerms]
  | cons row rows ih =>
      simp only [List.foldlM_cons, List.map_cons, evalTerms, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, bind_assoc, pure_bind, map_bind]
      congr 1
      funext answer
      rw [ih]
      simp only [map_pure, bind_pure_comp]
      congr 1
      funext value
      exact add_assoc acc (row.2 • answer) value

variable {G₁ G₂ : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq M]
  (cost : PrimitiveCosts)

theorem evaluateRows_source {value : Ty CryptoAtom}
    [AddCommMonoid (value.Value (cryptoBase F G₁ G₂ M M))]
    [SMul F (value.Value (cryptoBase F G₁ G₂ M M))]
    (impl : QueryImpl (baseSpec M (value.Value (cryptoBase F G₁ G₂ M M))) N)
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (hz : zero.denote (arithmetic F G₁ G₂ M M cost) (rows, default, ()) = 0)
    (hc : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ M M cost) (answer, coeff, acc, ()) =
      acc + coeff • answer) :
    (evaluateRows zero combine).denote (arithmetic F G₁ G₂ M M cost)
      (evalSemantics (fun m => impl (.inr m))) (rows, default, ()) =
      simulateQ impl (evalTerms (rows.map (fun row => (row.1.1, row.2)))) := by
  rw [evaluateRows_denote, hz]
  simp_rw [hc]
  simpa only [zero_add, id_map'] using
    (foldRows_simulate (F := F) (R := value.Value (cryptoBase F G₁ G₂ M M)) impl rows 0)

theorem evaluateGood_source (impl : QueryImpl (baseSpec M F) N)
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F) :
    evaluateGood.denote (arithmetic F G₁ G₂ M M cost) (evalSemantics (fun m => impl (.inr m)))
      (rows, default, ()) =
      simulateQ impl (evalTerms (rows.map (fun row => (row.1.1, row.2)))) := by
  exact evaluateRows_source cost impl (.op .zero .unit) goodCombine rows default rfl
    (fun answer coeff acc => goodCombine_denote (G₁ := G₁) (G₂ := G₂) (M := M) cost answer coeff acc)

theorem evaluateBad_source (impl : QueryImpl (baseSpec M (F × F)) N)
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F) :
    evaluateBad.denote (arithmetic F G₁ G₂ M M cost) (evalSemantics (fun m => impl (.inr m)))
      (rows, default, ()) =
      simulateQ impl (evalTerms (rows.map (fun row => (row.1.1, row.2)))) := by
  exact evaluateRows_source cost impl (.pair (.op .zero .unit) (.op .zero .unit)) badCombine rows default rfl
    (fun answer coeff acc => badCombine_denote (G₁ := G₁) (G₂ := G₂) (M := M) cost answer acc coeff)

end Signatures.Runtime.LazyAGM
