import Signatures.Runtime.WeightedCoefficients
import Signatures.Runtime.WeightedEvaluateSource
import Signatures.Runtime.WeightedReply
import Signatures.Runtime.Extraction

/-! First-order weighted AGM extraction. Chronological hash coefficients and
expanded signing coefficients are evaluated in source order, followed by the
final message's full term list. All phases use one private cache. Zero terms,
missing coefficients and division by zero retain their source semantics. -/

open OracleComp OracleSpec Model.LazyAGM

namespace Signatures.Runtime.WeightedAGM.Extract

open LazyAGM.ReplySyntax Evaluate

variable {indexTy messageTy value : Ty CryptoAtom}

/-- A hash reply contributes its one base with weight one. This lets the same
chronological coefficient routine handle both kinds of transcript. -/
def hashTerms : Expr CryptoOp [indexTy] (.list (Terms.termTy indexTy)) :=
  .cons (.pair v0 (.op .one .unit)) .nil

def evaluateCoefficients {dataTy : Ty CryptoAtom}
    (terms : Expr CryptoOp [dataTy] (.list (Terms.termTy indexTy)))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    Program CryptoOp (EvalCmd indexTy value)
      [.list (AGM.tokenTy dataTy), .list scalar, evalRowTy indexTy] value :=
  .bind (.call (.ret (Coefficients.signedTerms terms)) (.cons v0 (.cons v1 .nil)))
    (.call (evaluateRows zero combine) (.cons v0 (.cons v3 .nil)))

def evaluateTarget (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value) :
    Program CryptoOp (EvalCmd indexTy value) [messageTy, evalRowTy indexTy] value :=
  .bind (.call (.ret terms) (.cons v0 .nil))
    (.call (evaluateRows zero combine) (.cons v0 (.cons v2 .nil)))

def defaultRow (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy)) :
    Expr CryptoOp [AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy] (evalRowTy indexTy) :=
  .letE (.fst v0) (default.weakenTail [AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy])

def good (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy)) :
    Program CryptoOp (EvalCmd indexTy scalar) [AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy] scalar :=
  .bind (.ret (defaultRow default))
    (.bind (.call (evaluateCoefficients hashTerms (.op .zero .unit) goodCombine)
      (.cons (.fst v2) (.cons (.fst (.snd (.snd v1))) (.cons v0 .nil))))
      (.bind (.call (evaluateCoefficients terms (.op .zero .unit) goodCombine)
        (.cons (.snd v3) (.cons (.snd (.snd (.snd v2))) (.cons v1 .nil))))
        (.bind (.call (evaluateTarget terms (.op .zero .unit) goodCombine)
          (.cons (.fst v3) (.cons v2 .nil)))
          (.ret (.op .div (.pair (.op .add (.pair (.fst (.snd v4)) v2))
            (.op .sub (.pair v0 v1))))))))

def bad (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy)) :
    Program CryptoOp (EvalCmd indexTy (.pair scalar scalar))
      [AGM.outputTy messageTy, Reply.transcriptTy indexTy messageTy] scalar :=
  .bind (.ret (defaultRow default))
    (.bind (.call (evaluateCoefficients terms (.pair (.op .zero .unit) (.op .zero .unit)) badCombine)
      (.cons (.snd v2) (.cons (.snd (.snd (.snd v1))) (.cons v0 .nil))))
      (.bind (.call (evaluateTarget terms (.pair (.op .zero .unit) (.op .zero .unit)) badCombine)
        (.cons (.fst v2) (.cons v1 .nil)))
        (.ret (.op .div (.pair (.op .neg (.op .sub (.pair (.snd v0) (.snd v1))))
          (.op .sub (.pair (.fst v0) (.fst v1))))))))

section Source

variable {F ι M G₁ G₂ : Type} [Field F]

def goodFinish (terms : M → List (ι × F)) (out : Model.LazyAGM.Output F M)
    (tr : Model.LazyAGM.Transcript ι M G₁) : OracleComp (baseSpec ι F) F := do
  let hashes ← evalTerms (BLS.LazyAGM.Reduction.traceTerms out.γ tr.1)
  let signatures ← evalTerms (Model.LazyAGM.WeightedReduction.signedTerms terms out.ξ tr.2)
  let target ← evalTerms (terms out.mstar)
  pure ((out.β + hashes) / (target - signatures))

def badFinish (terms : M → List (ι × F)) (out : Model.LazyAGM.Output F M)
    (tr : Model.LazyAGM.Transcript ι M G₁) : OracleComp (baseSpec ι (F × F)) F := do
  let signatures ← evalTerms (Model.LazyAGM.WeightedReduction.signedTerms terms out.ξ tr.2)
  let target ← evalTerms (terms out.mstar)
  pure (-(target.2 - signatures.2) / (target.1 - signatures.1))

theorem hash_signedTerms (coeff : List F) (tr : List (ι × G₁)) :
    Model.LazyAGM.WeightedReduction.signedTerms (fun i => [(i, (1 : F))]) coeff tr =
      BLS.LazyAGM.Reduction.traceTerms coeff tr := by
  simp only [Model.LazyAGM.WeightedReduction.signedTerms, BLS.LazyAGM.Reduction.traceTerms,
    List.map_singleton, mul_one, List.mapIdx_eq_ofFn]
  simpa only [List.flatMap, List.map_ofFn, Function.comp_def] using
    List.flatMap_singleton' (List.ofFn fun i : Fin tr.length => ((tr.get i).1, tokenCoeff coeff i.val))

variable [AddCommGroup G₁] [Module F G₁]

theorem goodProgram_finish (terms : M → List (ι × F)) (g X : G₁) (pk : G₂)
    (A : Model.LazyAGM.Adversary F ι M G₁ G₂) :
    Model.LazyAGM.WeightedReduction.goodProgram terms g X pk A =
      (do let p ← Model.LazyAGM.WeightedReduction.privateRun terms
            (fun rho : F => rho • g) (fun rho => rho • X) A pk
          goodFinish terms p.1 p.2) := rfl

theorem badProgram_finish (terms : M → List (ι × F)) (g X : G₁) (pk : G₂) (kappa : F)
    (A : Model.LazyAGM.Adversary F ι M G₁ G₂) :
    Model.LazyAGM.WeightedReduction.badProgram terms g X pk kappa A =
      (do let p ← Model.LazyAGM.WeightedReduction.privateRun terms
            (fun masks : F × F => masks.1 • X + masks.2 • g)
            (fun masks => kappa • (masks.1 • X + masks.2 • g)) A pk
          badFinish terms p.1 p.2) := rfl

end Source

variable {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  (cost : PrimitiveCosts)
  {N : Type → Type} [Monad N] [LawfulMonad N]

theorem evaluateCoefficients_source {dataTy : Ty CryptoAtom}
    [AddCommMonoid (value.Value (cryptoBase F G₁ G₂ K M))]
    [SMul F (value.Value (cryptoBase F G₁ G₂ K M))]
    (impl : QueryImpl (baseSpec (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (value.Value (cryptoBase F G₁ G₂ K M))) N)
    (terms : Expr CryptoOp [dataTy] (.list (Terms.termTy indexTy)))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (hz : ∀ rows default, zero.denote (arithmetic F G₁ G₂ K M cost) (rows, default, ()) = 0)
    (hc : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ K M cost) (answer, coeff, acc, ()) =
      acc + coeff • answer)
    (tr : List (dataTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) :
    (evaluateCoefficients terms zero combine).denote (arithmetic F G₁ G₂ K M cost)
      (evalSemantics (fun i => impl (.inr i))) (tr, coeff, default, ()) =
      simulateQ impl (evalTerms (Model.LazyAGM.WeightedReduction.signedTerms
        (fun m => terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())) coeff tr.reverse)) := by
  simp only [evaluateCoefficients, Program.denote, pure_bind, Args.denote, v0, v1, v3, Expr.denote, Var.get]
  rw [evaluateRows_source cost impl zero combine _ default (hz _ default) hc,
    Coefficients.signedTerms_denote]

theorem evaluateTarget_source
    [AddCommMonoid (value.Value (cryptoBase F G₁ G₂ K M))]
    [SMul F (value.Value (cryptoBase F G₁ G₂ K M))]
    (impl : QueryImpl (baseSpec (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (value.Value (cryptoBase F G₁ G₂ K M))) N)
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (hz : ∀ rows default, zero.denote (arithmetic F G₁ G₂ K M cost) (rows, default, ()) = 0)
    (hc : ∀ answer coeff acc, combine.denote (arithmetic F G₁ G₂ K M cost) (answer, coeff, acc, ()) =
      acc + coeff • answer)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F) :
    (evaluateTarget terms zero combine).denote (arithmetic F G₁ G₂ K M cost)
      (evalSemantics (fun i => impl (.inr i))) (m, default, ()) =
      simulateQ impl (evalTerms (terms.denote (arithmetic F G₁ G₂ K M cost) (m, ()))) := by
  simp only [evaluateTarget, Program.denote, pure_bind, Args.denote, v0, v2, Expr.denote, Var.get]
  rw [evaluateRows_source cost impl zero combine _ default (hz _ default) hc]

theorem good_source
    (impl : QueryImpl (baseSpec (indexTy.Value (cryptoBase F G₁ G₂ K M)) F) N)
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy))
    (out : (AGM.outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) :
    (good terms default).denote (arithmetic F G₁ G₂ K M cost)
      (evalSemantics (fun i => impl (.inr i))) (out, tr, ()) =
      simulateQ impl (goodFinish (fun m => terms.denote (arithmetic F G₁ G₂ K M cost) (m, ()))
        (AGM.outputView out) (Reply.chronological tr)) := by
  have hc := fun (answer coeff acc : F) => goodCombine_denote (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost answer coeff acc
  have hh := evaluateCoefficients_source (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost impl (hashTerms (indexTy := indexTy))
    (.op .zero .unit) goodCombine (fun _ _ => rfl) hc
  have hs := evaluateCoefficients_source (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost impl terms (.op .zero .unit) goodCombine (fun _ _ => rfl) hc
  have ht := evaluateTarget_source (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost impl terms (.op .zero .unit) goodCombine (fun _ _ => rfl) hc
  simp only [good, Program.denote, pure_bind, Args.denote, v0, v1, v2, v3, v4,
    hs, ht, Expr.denote, Var.get,
    goodFinish, Reply.chronological, AGM.outputView, simulateQ_bind, simulateQ_pure]
  have hid : (fun m => (hashTerms (indexTy := indexTy)).denote
      (arithmetic F G₁ G₂ K M cost) (m, ())) =
      (fun m : indexTy.Value (cryptoBase F G₁ G₂ K M) => [(m, (1 : F))]) := rfl
  rw [hh, hid, hash_signedTerms]
  rfl

theorem bad_source
    (impl : QueryImpl (baseSpec (indexTy.Value (cryptoBase F G₁ G₂ K M)) (F × F)) N)
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (default : Expr CryptoOp [messageTy] (Terms.termTy indexTy))
    (out : (AGM.outputTy messageTy).Value (cryptoBase F G₁ G₂ K M))
    (tr : Model.LazyAGM.Transcript (indexTy.Value (cryptoBase F G₁ G₂ K M))
      (messageTy.Value (cryptoBase F G₁ G₂ K M)) G₁) :
    (bad terms default).denote (arithmetic F G₁ G₂ K M cost)
      (evalSemantics (fun i => impl (.inr i))) (out, tr, ()) =
      simulateQ impl (badFinish (fun m => terms.denote (arithmetic F G₁ G₂ K M cost) (m, ()))
        (AGM.outputView out) (Reply.chronological tr)) := by
  have hc := fun (answer : F × F) (coeff : F) (acc : F × F) => badCombine_denote (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost answer acc coeff
  have hs := evaluateCoefficients_source (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost impl terms
    (.pair (.op .zero .unit) (.op .zero .unit)) badCombine (fun _ _ => rfl) hc
  have ht := evaluateTarget_source (G₁ := G₁) (G₂ := G₂) (K := K) (M := M) cost impl terms
    (.pair (.op .zero .unit) (.op .zero .unit)) badCombine (fun _ _ => rfl) hc
  simp only [bad, Program.denote, pure_bind, Args.denote, v0, v1, v2,
    hs, ht, Expr.denote, Var.get, badFinish, Reply.chronological, AGM.outputView,
    simulateQ_bind, simulateQ_pure]
  rfl

end Signatures.Runtime.WeightedAGM.Extract
