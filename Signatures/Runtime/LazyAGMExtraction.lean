import Signatures.Runtime.LazyAGMEvaluateSource
import Signatures.Runtime.Extraction
import Signatures.BLS.Spec.LazyAGMReduction

/-! Complete first-order lazy BLS AGM extraction. The good branch evaluates
hash and signature rows in that order; the bad branch evaluates signature rows
into scalar pairs. Both then access the final target and perform the source's
field arithmetic, including its division-by-zero behavior. -/

open OracleComp OracleSpec Model.LazyAGM

namespace Signatures.Runtime.LazyAGM

open ReplySyntax

def evaluateTokens {value : Ty CryptoAtom}
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    Program CryptoOp (EvalCmd value) [.list (AGM.tokenTy message), .list scalar, evalRowTy] value :=
  .bind (.ret ((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy]))
    (.call (evaluateRows zero combine) (.cons v0 (.cons v3 .nil)))

def defaultRow : Expr CryptoOp [AGM.outputTy message, transcriptTy] evalRowTy :=
  .pair (.pair (.fst v0) (.op .zero₁ .unit)) (.op .zero .unit)

def extractGood : Program CryptoOp (EvalCmd scalar) [AGM.outputTy message, transcriptTy] scalar :=
  .bind (.ret defaultRow)
    (.bind (.call (evaluateTokens (.op .zero .unit) goodCombine)
      (.cons (.fst v2) (.cons (.fst (.snd (.snd v1))) (.cons v0 .nil))))
      (.bind (.call (evaluateTokens (.op .zero .unit) goodCombine)
        (.cons (.snd v3) (.cons (.snd (.snd (.snd v2))) (.cons v1 .nil))))
        (.bind (.query .lookup (.fst v3))
          (.ret (.op .div (.pair (.op .add (.pair (.fst (.snd v4)) v2)) (.op .sub (.pair v0 v1))))))))

def extractBad : Program CryptoOp (EvalCmd (.pair scalar scalar)) [AGM.outputTy message, transcriptTy] scalar :=
  .bind (.ret defaultRow)
    (.bind (.call (evaluateTokens (.pair (.op .zero .unit) (.op .zero .unit)) badCombine)
      (.cons (.snd v2) (.cons (.snd (.snd (.snd v1))) (.cons v0 .nil))))
      (.bind (.query .lookup (.fst v2))
        (.ret (.op .div (.pair (.op .neg (.op .sub (.pair (.snd v0) (.snd v1))))
          (.op .sub (.pair (.fst v0) (.fst v1))))))))

variable {F G₁ G₂ M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq M]
  (cost : PrimitiveCosts)

theorem tokenRows_terms (tr : List (M × G₁)) (coeff : List F) (default : (M × G₁) × F) :
    (((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy]).denote (arithmetic F G₁ G₂ M M cost)
      (tr, coeff, default, ())).map (fun row => (row.1.1, row.2)) =
      BLS.LazyAGM.Reduction.traceTerms coeff tr.reverse := by
  have h := (AGM.tokenRows (dataTy := message)).weakenTail_denote (Δ := [evalRowTy]) (arithmetic F G₁ G₂ M M cost)
    (tr, coeff, ()) (default, ())
  simp only [Env.append] at h
  have hv := AGM.tokenRows_value (dataTy := message) (G₁ := G₁) (G₂ := G₂)
    (K := M) (M := M) cost tr coeff
  rw [Expr.run_value] at hv
  rw [h, hv]
  simp [BLS.LazyAGM.Reduction.traceTerms, List.mapIdx_eq_ofFn, List.map_ofFn, Function.comp_def]

variable {N : Type → Type} [Monad N] [LawfulMonad N]

theorem evaluateTokens_source {value : Ty CryptoAtom}
    [AddCommMonoid (value.Value (cryptoBase F G₁ G₂ M M))]
    [SMul F (value.Value (cryptoBase F G₁ G₂ M M))]
    (impl : QueryImpl (baseSpec M (value.Value (cryptoBase F G₁ G₂ M M))) N)
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (hz : ∀ rows default, zero.denote (arithmetic F G₁ G₂ M M cost) (rows, default, ()) = 0)
    (hc : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ M M cost) (answer, coeff, acc, ()) =
      acc + coeff • answer)
    (tr : List (M × G₁)) (coeff : List F) (default : (M × G₁) × F) :
    (evaluateTokens zero combine).denote (arithmetic F G₁ G₂ M M cost)
      (evalSemantics (fun m => impl (.inr m))) (tr, coeff, default, ()) =
      simulateQ impl (evalTerms (BLS.LazyAGM.Reduction.traceTerms coeff tr.reverse)) := by
  simp only [evaluateTokens, Program.denote, pure_bind, Args.denote, v0, v3, Expr.denote, Var.get]
  rw [evaluateRows_source cost _ zero combine _ default (hz _ default) hc, tokenRows_terms]

def goodFinish (out : Model.LazyAGM.Output F M) (tr : Model.LazyAGM.Transcript M M G₁) :
    OracleComp (baseSpec M F) F := do
  let hashes ← evalTerms (BLS.LazyAGM.Reduction.traceTerms out.γ tr.1)
  let signatures ← evalTerms (BLS.LazyAGM.Reduction.traceTerms out.ξ tr.2)
  let target : F ← liftM ((baseSpec M F).query (.inr out.mstar))
  pure ((out.β + hashes) / (target - signatures))

def badFinish (out : Model.LazyAGM.Output F M) (tr : Model.LazyAGM.Transcript M M G₁) :
    OracleComp (baseSpec M (F × F)) F := do
  let signatures ← evalTerms (BLS.LazyAGM.Reduction.traceTerms out.ξ tr.2)
  let target : F × F ← liftM ((baseSpec M (F × F)).query (.inr out.mstar))
  pure (-(target.2 - signatures.2) / (target.1 - signatures.1))

theorem extractGood_source (impl : QueryImpl (baseSpec M F) N)
    (out : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) :
    extractGood.denote (arithmetic F G₁ G₂ M M cost) (evalSemantics (fun m => impl (.inr m))) (out, tr, ()) =
      simulateQ impl (goodFinish (AGM.outputView out) (chronological tr)) := by
  have ht := evaluateTokens_source (G₁ := G₁) (G₂ := G₂) cost impl (.op .zero .unit) goodCombine
    (fun _ _ => rfl) (fun answer coeff acc => goodCombine_denote (G₁ := G₁) (G₂ := G₂) (M := M) cost answer coeff acc)
  simp only [extractGood, Program.denote, pure_bind, Args.denote, v0, v1, v2, v3, v4,
    ht, defaultRow, Expr.denote, Var.get, evalSemantics, goodFinish, chronological, AGM.outputView,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rfl

theorem extractBad_source (impl : QueryImpl (baseSpec M (F × F)) N)
    (out : (AGM.outputTy message).Value (cryptoBase F G₁ G₂ M M))
    (tr : Model.LazyAGM.Transcript M M G₁) :
    extractBad.denote (arithmetic F G₁ G₂ M M cost) (evalSemantics (fun m => impl (.inr m))) (out, tr, ()) =
      simulateQ impl (badFinish (AGM.outputView out) (chronological tr)) := by
  have ht := evaluateTokens_source (G₁ := G₁) (G₂ := G₂) cost impl
    (.pair (.op .zero .unit) (.op .zero .unit)) badCombine
    (fun _ _ => rfl) (fun answer coeff acc => badCombine_denote (G₁ := G₁) (G₂ := G₂) (M := M) cost answer acc coeff)
  simp only [extractBad, Program.denote, pure_bind, Args.denote, v0, v1, v2,
    ht, defaultRow, Expr.denote, Var.get, evalSemantics, badFinish, chronological, AGM.outputView,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  rfl

end Signatures.Runtime.LazyAGM
