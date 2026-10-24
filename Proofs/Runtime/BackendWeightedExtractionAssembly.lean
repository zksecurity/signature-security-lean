import Proofs.Runtime.BackendWeightedExtractionCost
import Proofs.Runtime.BackendWeightedEvaluate
import Proofs.Runtime.BackendLanguageBudget

/-! Runtime composition of actual preparation and evaluation calls. The pure
preparation runs in its own argument frame; native calls retain and charge the
full surrounding context and cache. Component budgets are discharged separately
by the generator and scalar/pair evaluator bounds. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Extract

open BackendProgram Evaluate

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
  {iface : Interface (C := C) unifSpec}
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include laws dataLaws primitiveBound sizes mono routing

attribute [local irreducible] Language.compile Expression.compile Expression.arguments

omit dataLaws primitiveBound in
private theorem prepareEvaluate_bound {Γ Δ Θ : List (Ty CryptoAtom)} {a b value indexTy}
    (reader : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.ty indexTy) (rep.ty (Reply.cacheTy indexTy value)))
      (rep.ty (Reply.cacheResultTy indexTy value)))
    (prepare : Expr CryptoOp Δ a) (prepareArgs : Args CryptoOp Γ Δ)
    (body : Program CryptoOp (EvalCmd indexTy value) Θ b) (evaluateArgs : Args CryptoOp (a :: Γ) Θ)
    (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (post : b.Value (cryptoBase F G₁ G₂ K M) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)) → Prop)
    (width argumentTime preparationTime nextArgumentTime evaluationTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env Γ) env ≤ width)
    (hs : Q.size (rep.ty (Reply.cacheTy indexTy value)) cache ≤ width)
    (hp : Q.size (rep.env Δ) (prepareArgs.denote (arithmetic F G₁ G₂ K M cost) env) ≤ width)
    (hr : Q.size (rep.ty a) (prepare.denote (arithmetic F G₁ G₂ K M cost)
      (prepareArgs.denote (arithmetic F G₁ G₂ K M cost) env)) ≤ width)
    (hm : Q.size (rep.env (a :: Γ)) (prepare.denote (arithmetic F G₁ G₂ K M cost)
      (prepareArgs.denote (arithmetic F G₁ G₂ K M cost) env), env) ≤ width)
    (he : Q.size (rep.env Θ) (evaluateArgs.denote (arithmetic F G₁ G₂ K M cost)
      (prepare.denote (arithmetic F G₁ G₂ K M cost)
        (prepareArgs.denote (arithmetic F G₁ G₂ K M cost) env), env)) ≤ width)
    (harg : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive prepareArgs) env ≤ argumentTime)
    (hprepare : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive prepare)
      (prepareArgs.denote (arithmetic F G₁ G₂ K M cost) env) ≤ preparationTime)
    (hnext : Q.cost (Expression.arguments rep data (arithmetic F G₁ G₂ K M cost) primitive evaluateArgs)
      (prepare.denote (arithmetic F G₁ G₂ K M cost)
        (prepareArgs.denote (arithmetic F G₁ G₂ K M cost) env), env) ≤ nextArgumentTime)
    (hbody : ∀ z ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
        (rep.ty (Reply.cacheTy indexTy value)) (readEffect rep reader) body).run control queryCost
          (evaluateArgs.denote (arithmetic F G₁ G₂ K M cost)
            (prepare.denote (arithmetic F G₁ G₂ K M cost)
              (prepareArgs.denote (arithmetic F G₁ G₂ K M cost) env), env), cache)),
      post z.value ∧ z.steps ≤ evaluationTime)
    (out : Run (b.Value (cryptoBase F G₁ G₂ K M) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
        (rep.ty (Reply.cacheTy indexTy value)) (readEffect rep reader)
        (.bind (.call (.ret prepare) prepareArgs) (.call body evaluateArgs))).run control queryCost (env, cache))) :
    post out.value ∧ out.steps ≤ argumentTime + preparationTime + nextArgumentTime + evaluationTime +
      28 * overhead (32 * width) := by
  let P := arithmetic F G₁ G₂ K M cost
  let effect : {x y : Ty CryptoAtom} → EvalCmd indexTy value x y →
      Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty x) (rep.ty (Reply.cacheTy indexTy value)))
        (StepClass.HasProd.prod (rep.ty y) (rep.ty (Reply.cacheTy indexTy value))) :=
    readEffect rep reader
  let args := prepareArgs.denote P env
  let rows := prepare.denote P args
  let target := evaluateArgs.denote P (rows, env)
  let pre := fun e => e = env
  let middle := fun r => r = rows
  let saved := fun c => c = cache
  let fee := overhead (32 * width)
  have hret := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (Reply.cacheTy indexTy value)) effect prepare (fun e => e = args) middle saved width preparationTime
    (by intro e he'; subst e; exact hp)
    (by intro c hc; subst c; exact hs)
    (by intro e he'; subst e; exact ⟨rfl, hr⟩)
    (by intro e he'; subst e; exact hprepare)
  have hfirst := Language.call_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (Reply.cacheTy indexTy value)) effect (.ret prepare) prepareArgs pre (fun e => e = args) saved
    (fun p => middle p.1 ∧ saved p.2) width argumentTime (preparationTime + 2 * fee) hh
    (by intro e he'; subst e; exact hi)
    (by intro c hc; subst c; exact hs)
    (by intro e he'; subst e; exact ⟨rfl, hp⟩)
    (by intro e he'; subst e; exact harg) hret
  have hlast := Language.call_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (Reply.cacheTy indexTy value)) effect body evaluateArgs (fun e => middle e.1 ∧ pre e.2)
    (fun e => e = target) saved post width nextArgumentTime evaluationTime hh
    (by intro e he'; have heq : e = (rows, env) := Prod.ext he'.1 he'.2; rw [heq]; exact hm)
    (by intro c hc; subst c; exact hs)
    (by intro e he'; have heq : e = (rows, env) := Prod.ext he'.1 he'.2; rw [heq]; exact ⟨rfl, he⟩)
    (by intro e he'; have heq : e = (rows, env) := Prod.ext he'.1 he'.2; rw [heq]; exact hnext)
    (by
      intro input hp' z hz
      have heq : input = (target, cache) := Prod.ext hp'.1 hp'.2
      rw [heq] at hz
      exact hbody z hz)
  have h := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (Reply.cacheTy indexTy value)) effect (.call (.ret prepare) prepareArgs) (.call body evaluateArgs)
    pre middle saved post width (argumentTime + (preparationTime + 2 * fee) + 3 * fee)
    (nextArgumentTime + evaluationTime + 3 * fee) hh
    (by intro e he'; subst e; exact hi)
    (by intro r hr'; subst r; exact hr)
    (by intro c hc; subst c; exact hs) hfirst hlast
  have hbound := h (env, cache) ⟨rfl, rfl⟩ out hout
  exact ⟨hbound.1, by omega⟩

theorem evaluateCoefficients_bound {indexTy messageTy value : Ty CryptoAtom}
    (reader : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.ty indexTy) (rep.ty (Reply.cacheTy indexTy value)))
      (rep.ty (Reply.cacheResultTy indexTy value)))
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (tr : List (messageTy.Value (cryptoBase F G₁ G₂ K M) × G₁)) (coeff : List F)
    (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (post : value.Value (cryptoBase F G₁ G₂ K M) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)) → Prop)
    (width preparationTime evaluationTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [.list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy]) (tr, coeff, default, ()) ≤ width)
    (hs : Q.size (rep.ty (Reply.cacheTy indexTy value)) cache ≤ width)
    (hr : Q.size (rep.ty (.list (evalRowTy indexTy)))
      ((Coefficients.signedTerms terms).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ())) ≤ width)
    (ht : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (Coefficients.signedTerms terms))
      (tr, coeff, ()) ≤ preparationTime)
    (he : ∀ z ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Reply.cacheTy indexTy value)) (readEffect rep reader) (evaluateRows zero combine)).run control queryCost
        (((Coefficients.signedTerms terms).denote (arithmetic F G₁ G₂ K M cost) (tr, coeff, ()), default, ()), cache)),
      post z.value ∧ z.steps ≤ evaluationTime)
    (out : Run (value.Value (cryptoBase F G₁ G₂ K M) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Reply.cacheTy indexTy value)) (readEffect rep reader) (evaluateCoefficients terms zero combine)).run
        control queryCost ((tr, coeff, default, ()), cache))) :
    post out.value ∧ out.steps ≤ preparationTime + evaluationTime + 64 * overhead (1024 * width) := by
  let P := arithmetic F G₁ G₂ K M cost
  let env : Env (cryptoBase F G₁ G₂ K M) [.list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy] := (tr, coeff, default, ())
  let rows := (Coefficients.signedTerms terms).denote P (tr, coeff, ())
  have hw : width ≤ 8 * width := by omega
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hprepare : Q.size (rep.env [.list (AGM.tokenTy messageTy), .list scalar]) (tr, coeff, ()) ≤ 8 * width := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have hframe : Q.size (rep.env (.list (evalRowTy indexTy) :: [.list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy])) (rows, env) ≤ 8 * width := by
    have h := sizes.prod_le (rep.ty (.list (evalRowTy indexTy))) (rep.env [.list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy]) (rows, env)
    change Q.size (rep.env (.list (evalRowTy indexTy) :: [.list (AGM.tokenTy messageTy), .list scalar, evalRowTy indexTy])) (rows, env) ≤ _ at h
    exact h.trans (by change Q.size (rep.ty (.list (evalRowTy indexTy))) rows ≤ width at hr; dsimp only [env] at *; omega)
  have heval : Q.size (rep.env [.list (evalRowTy indexTy), evalRowTy indexTy]) (rows, default, ()) ≤ 8 * width := by
    dsimp only [env, rows, P, LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have harg := coefficientPrepareArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (tr, coeff, default, ()) (8 * width) (hh.trans hw) (hu.trans hw) (hi.trans hw)
  have hnext := coefficientEvaluateArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (rows, env) (8 * width) (hh.trans hw) (hu.trans hw) hframe
  have h := prepareEvaluate_bound rep data cost primitive laws sizes mono control queryCost routing
    reader (Coefficients.signedTerms terms) coefficientPrepareArgs (evaluateRows zero combine) coefficientEvaluateArgs env cache post
    (8 * width) (16 * overhead (128 * (8 * width))) preparationTime
    (16 * overhead (128 * (8 * width))) evaluationTime (hh.trans hw) (hi.trans hw) (hs.trans hw)
    hprepare (hr.trans hw) hframe heval harg ht hnext he out hout
  have hfee : overhead (32 * (8 * width)) ≤ overhead (1024 * width) := mono (by omega)
  have hscale : 128 * (8 * width) = 1024 * width := by omega
  rw [hscale] at h
  exact ⟨h.1, by omega⟩

theorem evaluateTarget_bound {indexTy messageTy value : Ty CryptoAtom}
    (reader : Code Q unifSpec iface
      (StepClass.HasProd.prod (rep.ty indexTy) (rep.ty (Reply.cacheTy indexTy value)))
      (rep.ty (Reply.cacheResultTy indexTy value)))
    (terms : Expr CryptoOp [messageTy] (.list (Terms.termTy indexTy)))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), evalRowTy indexTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (m : messageTy.Value (cryptoBase F G₁ G₂ K M))
    (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (post : value.Value (cryptoBase F G₁ G₂ K M) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)) → Prop)
    (width preparationTime evaluationTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [messageTy, evalRowTy indexTy]) (m, default, ()) ≤ width)
    (hs : Q.size (rep.ty (Reply.cacheTy indexTy value)) cache ≤ width)
    (hr : Q.size (rep.ty (.list (evalRowTy indexTy)))
      (terms.denote (arithmetic F G₁ G₂ K M cost) (m, ())) ≤ width)
    (ht : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive terms)
      (m, ()) ≤ preparationTime)
    (he : ∀ z ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Reply.cacheTy indexTy value)) (readEffect rep reader) (evaluateRows zero combine)).run control queryCost
        ((terms.denote (arithmetic F G₁ G₂ K M cost) (m, ()), default, ()), cache)),
      post z.value ∧ z.steps ≤ evaluationTime)
    (out : Run (value.Value (cryptoBase F G₁ G₂ K M) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (Reply.cacheTy indexTy value)) (readEffect rep reader) (evaluateTarget terms zero combine)).run
        control queryCost ((m, default, ()), cache))) :
    post out.value ∧ out.steps ≤ preparationTime + evaluationTime + 64 * overhead (1024 * width) := by
  let P := arithmetic F G₁ G₂ K M cost
  let env : Env (cryptoBase F G₁ G₂ K M) [messageTy, evalRowTy indexTy] := (m, default, ())
  let rows := terms.denote P (m, ())
  have hw : width ≤ 8 * width := by omega
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hprepare : Q.size (rep.env [messageTy]) (m, ()) ≤ 8 * width := by
    dsimp only [LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have hframe : Q.size (rep.env (.list (evalRowTy indexTy) :: [messageTy, evalRowTy indexTy])) (rows, env) ≤ 8 * width := by
    have h := sizes.prod_le (rep.ty (.list (evalRowTy indexTy))) (rep.env [messageTy, evalRowTy indexTy]) (rows, env)
    change Q.size (rep.env (.list (evalRowTy indexTy) :: [messageTy, evalRowTy indexTy])) (rows, env) ≤ _ at h
    exact h.trans (by change Q.size (rep.ty (.list (evalRowTy indexTy))) rows ≤ width at hr; dsimp only [env] at *; omega)
  have heval : Q.size (rep.env [.list (evalRowTy indexTy), evalRowTy indexTy]) (rows, default, ()) ≤ 8 * width := by
    dsimp only [env, rows, P, LanguageRepresentation.env, LanguageRepresentation.ty] at *
    grind only
  have harg := targetPrepareArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (m, default, ()) (8 * width) (hh.trans hw) (hu.trans hw) (hi.trans hw)
  have hnext := targetEvaluateArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (rows, env) (8 * width) (hh.trans hw) (hu.trans hw) hframe
  have h := prepareEvaluate_bound rep data cost primitive laws sizes mono control queryCost routing
    reader terms targetPrepareArgs (evaluateRows zero combine) targetEvaluateArgs env cache post
    (8 * width) (16 * overhead (128 * (8 * width))) preparationTime
    (16 * overhead (128 * (8 * width))) evaluationTime (hh.trans hw) (hi.trans hw) (hs.trans hw)
    hprepare (hr.trans hw) hframe heval harg ht hnext he out hout
  have hfee : overhead (32 * (8 * width)) ≤ overhead (1024 * width) := mono (by omega)
  have hscale : 128 * (8 * width) = 1024 * width := by omega
  rw [hscale] at h
  exact ⟨h.1, by omega⟩

end Signatures.Runtime.WeightedAGM.Extract
