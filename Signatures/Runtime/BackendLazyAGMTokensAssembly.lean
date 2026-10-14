import Signatures.Runtime.BackendLazyAGMExtractionCost
import Signatures.Runtime.BackendLanguageBudget

/-! Native composition of chronological coefficient preparation and effectful
row evaluation, including the actual call arguments and retained preparation
context. Component contracts are instantiated by the branch budget modules. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include laws dataLaws primitiveBound sizes mono routing

-- Compose certificates without normalizing the implemented local code.
attribute [local irreducible] Language.compile Expression.compile Expression.arguments

theorem evaluatePreparedTokens_bound {value : Ty CryptoAtom}
    (prepare : Expr CryptoOp [.list (AGM.tokenTy message), .list scalar, evalRowTy] (.list evalRowTy))
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value)
    (body : Program CryptoOp (EvalCmd value) [.list evalRowTy, evalRowTy] value)
    (tr : List (M × G₁)) (coeff : List F) (default : (M × G₁) × F)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (width preparationTime evaluationTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [.list (AGM.tokenTy message), .list scalar, evalRowTy]) (tr, coeff, default, ()) ≤ width)
    (hs : Q.size (rep.ty (cacheTy value)) cache ≤ width)
    (hr : Q.size (rep.ty (.list evalRowTy))
      (prepare.denote (arithmetic F G₁ G₂ M M cost)
        (tr, coeff, default, ())) ≤ width)
    (ht : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      prepare) (tr, coeff, default, ()) ≤ preparationTime)
    (he : ∀ out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy value))
        (readEffect rep data cost primitive (value := value) sampler fallback) body).run control queryCost
        ((prepare.denote (arithmetic F G₁ G₂ M M cost)
          (tr, coeff, default, ()), default, ()), cache)),
      (Q.size (rep.ty value) out.value.1 ≤ width ∧ Q.size (rep.ty (cacheTy value)) out.value.2 ≤ width) ∧
        out.steps ≤ evaluationTime)
    (out : Run (value.Value (cryptoBase F G₁ G₂ M M) × List (M × value.Value (cryptoBase F G₁ G₂ M M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy value))
      (readEffect rep data cost primitive (value := value) sampler fallback)
      (.bind (.ret prepare) (.call body evaluateTokenArgs))).run
        control queryCost ((tr, coeff, default, ()), cache))) :
    (Q.size (rep.ty value) out.value.1 ≤ width ∧ Q.size (rep.ty (cacheTy value)) out.value.2 ≤ width) ∧
      out.steps ≤ preparationTime + evaluationTime + 64 * overhead (512 * width) := by
  let P := arithmetic F G₁ G₂ M M cost
  let env : Env (cryptoBase F G₁ G₂ M M) [.list (AGM.tokenTy message), .list scalar, evalRowTy] :=
    (tr, coeff, default, ())
  let rows := prepare.denote P env
  let effect : {a b : Ty CryptoAtom} → EvalCmd value a b →
      Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty (cacheTy value)))
        (StepClass.HasProd.prod (rep.ty b) (rep.ty (cacheTy value))) :=
    readEffect rep data cost primitive (value := value) sampler fallback
  let fee := overhead (32 * (3 * width))
  let argFee := overhead (128 * (3 * width))
  let pre := fun e => e = env
  let middle := fun r => r = rows
  let saved := fun c => c = cache
  let post := fun p : value.Value (cryptoBase F G₁ G₂ M M) × List (M × value.Value (cryptoBase F G₁ G₂ M M)) =>
    Q.size (rep.ty value) p.1 ≤ width ∧ Q.size (rep.ty (cacheTy value)) p.2 ≤ width
  have h3 : width ≤ 3 * width := by omega
  have henv : Q.size (rep.env [.list (AGM.tokenTy message), .list scalar, evalRowTy]) env ≤ width := hi
  have hrows : Q.size (rep.ty (.list evalRowTy)) rows ≤ width := hr
  have hframe : Q.size (rep.env [.list evalRowTy, .list (AGM.tokenTy message), .list scalar, evalRowTy]) (rows, env) ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty (.list evalRowTy))
      (rep.env [.list (AGM.tokenTy message), .list scalar, evalRowTy]) (rows, env)
    change Q.size (rep.env [.list evalRowTy, .list (AGM.tokenTy message), .list scalar, evalRowTy]) (rows, env) ≤ _ at h
    dsimp only at h
    omega
  have hargs : Q.size (rep.env [.list evalRowTy, evalRowTy]) (rows, default, ()) ≤ 3 * width := by
    have htail : Q.size (rep.env [evalRowTy]) (default, ()) ≤ width :=
      (sizes.snd_le (rep.ty (.list scalar)) (rep.env [evalRowTy]) (coeff, default, ())).trans
        ((sizes.snd_le (rep.ty (.list (AGM.tokenTy message))) (rep.env [.list scalar, evalRowTy])
          (tr, coeff, default, ())).trans hi)
    have h := sizes.prod_le (rep.ty (.list evalRowTy)) (rep.env [evalRowTy]) (rows, default, ())
    change Q.size (rep.env [.list evalRowTy, evalRowTy]) (rows, default, ()) ≤ _ at h
    dsimp only at h
    omega
  have hargCost := evaluateTokenArgs_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (rows, env) (3 * width) (hh.trans h3) (hu.trans h3) hframe
  have hret := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy value)) effect prepare
    pre middle saved (3 * width) preparationTime
    (by intro e he'; change e = env at he'; rw [he']; exact henv.trans h3)
    (by intro c hc; change c = cache at hc; rw [hc]; exact hs.trans h3)
    (by intro e he'; change e = env at he'; rw [he']; exact ⟨rfl, hrows.trans h3⟩)
    (by intro e he'; change e = env at he'; rw [he']; exact ht)
  have hcall := Language.call_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy value)) effect body evaluateTokenArgs
    (fun e => middle e.1 ∧ pre e.2) (fun args => args = (rows, default, ())) saved post
    (3 * width) (16 * argFee) evaluationTime (hh.trans h3)
    (by
      intro e hp
      have heq : e = (rows, env) := Prod.ext hp.1 hp.2
      rw [heq]
      exact hframe)
    (by intro c hc; change c = cache at hc; rw [hc]; exact hs.trans h3)
    (by
      intro e hp
      have heq : e = (rows, env) := Prod.ext hp.1 hp.2
      rw [heq]
      exact ⟨rfl, hargs⟩)
    (by
      intro e hp
      have heq : e = (rows, env) := Prod.ext hp.1 hp.2
      rw [heq]
      exact hargCost)
    (by
      intro input hp z hz
      have heq : input = ((rows, default, ()), cache) := Prod.ext hp.1 hp.2
      have hz' : z ∈ support ((Language.compile rep data P primitive (rep.ty (cacheTy value)) effect
          body).run control queryCost ((rows, default, ()), cache)) :=
        heq ▸ hz
      exact he z hz')
  have hbnd := Language.bind_bound_of_width sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy value)) effect (.ret prepare)
    (.call body evaluateTokenArgs) pre middle saved post (3 * width)
    (preparationTime + 2 * fee) (16 * argFee + evaluationTime + 3 * fee) (hh.trans h3)
    (by intro e he'; change e = env at he'; rw [he']; exact henv.trans h3)
    (by intro r hr'; change r = rows at hr'; rw [hr']; exact hrows.trans h3)
    (by intro c hc; change c = cache at hc; rw [hc]; exact hs.trans h3) hret hcall
  have h := hbnd (env, cache) ⟨rfl, rfl⟩ out hout
  have hf1 : fee ≤ overhead (512 * width) := mono (by omega)
  have hf2 : argFee ≤ overhead (512 * width) := mono (by omega)
  exact ⟨h.1, by omega⟩

theorem evaluateTokens_bound {value : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value)
    (zero : Expr CryptoOp [.list evalRowTy, evalRowTy] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (tr : List (M × G₁)) (coeff : List F) (default : (M × G₁) × F)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (width preparationTime evaluationTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width)
    (hi : Q.size (rep.env [.list (AGM.tokenTy message), .list scalar, evalRowTy]) (tr, coeff, default, ()) ≤ width)
    (hs : Q.size (rep.ty (cacheTy value)) cache ≤ width)
    (hr : Q.size (rep.ty (.list evalRowTy))
      (((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy]).denote (arithmetic F G₁ G₂ M M cost)
        (tr, coeff, default, ())) ≤ width)
    (ht : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      ((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy])) (tr, coeff, default, ()) ≤ preparationTime)
    (he : ∀ out ∈ support ((backendEvaluate rep data cost primitive (value := value) sampler fallback zero combine).run control queryCost
        ((((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy]).denote (arithmetic F G₁ G₂ M M cost)
          (tr, coeff, default, ()), default, ()), cache)),
      (Q.size (rep.ty value) out.value.1 ≤ width ∧ Q.size (rep.ty (cacheTy value)) out.value.2 ≤ width) ∧
        out.steps ≤ evaluationTime)
    (out : Run (value.Value (cryptoBase F G₁ G₂ M M) × List (M × value.Value (cryptoBase F G₁ G₂ M M))))
    (hout : out ∈ support ((backendEvaluateTokens rep data cost primitive (value := value) sampler fallback zero combine).run control queryCost ((tr, coeff, default, ()), cache))) :
    (Q.size (rep.ty value) out.value.1 ≤ width ∧ Q.size (rep.ty (cacheTy value)) out.value.2 ≤ width) ∧
      out.steps ≤ preparationTime + evaluationTime + 64 * overhead (512 * width) := by
  have hsyntax : evaluateTokens (value := value) zero combine =
      .bind (.ret ((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy]))
        (.call (evaluateRows (value := value) zero combine) evaluateTokenArgs) := rfl
  have hcode : backendEvaluateTokens rep data cost primitive (value := value) sampler fallback zero combine =
      Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy value))
        (readEffect rep data cost primitive (value := value) sampler fallback)
        (.bind (.ret ((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy]))
          (.call (evaluateRows (value := value) zero combine) evaluateTokenArgs)) := by
    unfold backendEvaluateTokens
    exact congrArg (fun program : Program CryptoOp (EvalCmd value)
      [.list (AGM.tokenTy message), .list scalar, evalRowTy] value =>
        Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy value))
          (readEffect rep data cost primitive (value := value) sampler fallback) program) hsyntax
  have hout' := (congrArg (fun code => out ∈ support
    (code.run control queryCost ((tr, coeff, default, ()), cache))) hcode).mp hout
  have hecode : backendEvaluate rep data cost primitive (value := value) sampler fallback zero combine =
      Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (rep.ty (cacheTy value))
        (readEffect rep data cost primitive (value := value) sampler fallback) (evaluateRows (value := value) zero combine) := by
    rw [backendEvaluate]
  have he' := fun z hz => he z ((congrArg (fun code => z ∈ support (code.run control queryCost
    ((((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy]).denote (arithmetic F G₁ G₂ M M cost)
      (tr, coeff, default, ()), default, ()), cache))) hecode).mpr hz)
  exact evaluatePreparedTokens_bound rep data cost primitive laws dataLaws primitiveBound sizes mono
    control queryCost routing (value := value) ((AGM.tokenRows (dataTy := message)).weakenTail [evalRowTy])
    sampler fallback (evaluateRows (value := value) zero combine) tr coeff default cache
    width preparationTime evaluationTime hh hu hi hs hr ht he' out hout'


end Signatures.Runtime.LazyAGM
