import Proofs.Runtime.BackendLazyAGMEvaluate
import Proofs.Runtime.BackendLanguageBudget

/-! Composition of one implemented evaluator iteration. Selection, private
access, and arithmetic costs are joined with the native compiler's context,
query-argument, retention, invocation, and sequencing costs. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.LazyAGM

open BackendProgram ReplySyntax

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ M M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ M M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include sizes mono laws dataLaws primitiveBound

theorem evalKey_cost {Γ : List (Ty CryptoAtom)}
    (env : Env (cryptoBase F G₁ G₂ M M) (evalRowTy :: Γ)) (width : Nat)
    (hi : Q.size (rep.env (evalRowTy :: Γ)) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (.fst (.fst (.var .here)) : Expr CryptoOp (evalRowTy :: Γ) message)) env ≤
        5 * overhead (16 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ M M cost) primitive
    laws dataLaws primitiveBound _ env).trans ?_
  have hf := @sizes.fst_le
  have hs := @sizes.snd_le
  have hfee : ∀ k ≤ 16 * width, overhead k ≤ overhead (16 * width) := fun _ hk => mono hk
  dsimp only [Expression.compileBound, Expression.variableBound, LocalBound.compose,
    LocalBound.fst, Expr.denote, Var.get, LanguageRepresentation.env, LanguageRepresentation.ty] at *
  grind only

variable (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include routing

theorem evalBody_bound {value : Ty CryptoAtom}
    (sampler : Code Q unifSpec iface rep.data.unit (rep.ty value))
    (fallback : Expr CryptoOp [message, cacheTy value] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ M M))
    (rows : List ((M × G₁) × F)) (default : (M × G₁) × F)
    (cache : List (M × value.Value (cryptoBase F G₁ G₂ M M)))
    (width selectTime readTime updateTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [evalStateTy value, .list evalRowTy, evalRowTy])
      ((n, acc), rows, default, ()) ≤ width)
    (hs : Q.size (rep.ty (cacheTy value)) cache ≤ width)
    (hr : Q.size (rep.ty evalRowTy)
      ((selectRow (value := value)).denote (arithmetic F G₁ G₂ M M cost)
        ((n, acc), rows, default, ())) ≤ width)
    (ht : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (selectRow (value := value))) ((n, acc), rows, default, ()) ≤ selectTime)
    (hread : ∀ z ∈ support ((backendRead rep data cost primitive sampler fallback).run control queryCost
        (((selectRow (value := value)).denote (arithmetic F G₁ G₂ M M cost)
          ((n, acc), rows, default, ())).1.1, cache)),
      (Q.size (rep.ty value) z.value.1 ≤ width ∧ Q.size (rep.ty (cacheTy value)) z.value.2 ≤ width) ∧
        z.steps ≤ readTime)
    (hupdate : ∀ answer, Q.size (rep.ty value) answer ≤ width →
      Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ M M cost) primitive (evalUpdate combine))
        (answer, (selectRow (value := value)).denote (arithmetic F G₁ G₂ M M cost)
          ((n, acc), rows, default, ()), (n, acc), rows, default, ()) ≤ updateTime)
    (hresult : ∀ answer, Q.size (rep.ty value) answer ≤ width →
      Q.size (rep.ty (evalStateTy value))
        ((evalUpdate combine).denote (arithmetic F G₁ G₂ M M cost)
          (answer, (selectRow (value := value)).denote (arithmetic F G₁ G₂ M M cost)
            ((n, acc), rows, default, ()), (n, acc), rows, default, ())) ≤ width)
    (out : Run ((Nat × value.Value (cryptoBase F G₁ G₂ M M)) ×
      List (M × value.Value (cryptoBase F G₁ G₂ M M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ M M cost) primitive
      (rep.ty (cacheTy value)) (readEffect rep data cost primitive sampler fallback)
      (evalBody combine)).run control queryCost (((n, acc), rows, default, ()), cache))) :
    (Q.size (rep.ty (evalStateTy value)) out.value.1 ≤ width ∧
      Q.size (rep.ty (cacheTy value)) out.value.2 ≤ width) ∧
      out.steps ≤ selectTime + readTime + updateTime + 64 * overhead (256 * width) := by
  let P := arithmetic F G₁ G₂ M M cost
  let effect : {a b : Ty CryptoAtom} → EvalCmd value a b →
      Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty (cacheTy value)))
        (StepClass.HasProd.prod (rep.ty b) (rep.ty (cacheTy value))) :=
    readEffect rep data cost primitive sampler fallback
  let env : Env (cryptoBase F G₁ G₂ M M) [evalStateTy value, .list evalRowTy, evalRowTy] :=
    ((n, acc), rows, default, ())
  let row := (selectRow (value := value)).denote P env
  let fee := overhead (32 * (5 * width))
  have h5 : width ≤ 5 * width := by omega
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hrow : Q.size (rep.ty evalRowTy) row ≤ width := hr
  have henv : Q.size (rep.env [evalStateTy value, .list evalRowTy, evalRowTy]) env ≤ width := hi
  have hrowEnv : Q.size (rep.env [evalRowTy, evalStateTy value, .list evalRowTy, evalRowTy])
      (row, env) ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty evalRowTy) (rep.env [evalStateTy value, .list evalRowTy, evalRowTy]) (row, env)
    dsimp only at h
    exact h.trans (by omega)
  have hupdateEnv (answer : value.Value (cryptoBase F G₁ G₂ M M))
      (ha : Q.size (rep.ty value) answer ≤ width) :
      Q.size (rep.env [value, evalRowTy, evalStateTy value, .list evalRowTy, evalRowTy])
        (answer, row, env) ≤ 5 * width := by
    have h := sizes.prod_le (rep.ty value)
      (rep.env [evalRowTy, evalStateTy value, .list evalRowTy, evalRowTy]) (answer, row, env)
    dsimp only at h
    exact h.trans (by omega)
  have hkeySize : Q.size (rep.ty message) row.1.1 ≤ width := by
    dsimp only [evalRowTy, AGM.tokenTy, LanguageRepresentation.ty] at *
    grind only
  have hkey := evalKey_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (row, env) (3 * width) hrowEnv
  have hkeyFee : overhead (16 * (3 * width)) ≤ fee := mono (by omega)
  let pre := fun e => e = env
  let middle := fun r => r = row
  let saved := fun c => c = cache
  let answerOK := fun a => Q.size (rep.ty value) a ≤ width
  let cacheOK := fun c => Q.size (rep.ty (cacheTy value)) c ≤ width
  let finalOK := fun p : (Nat × value.Value (cryptoBase F G₁ G₂ M M)) ×
      List (M × value.Value (cryptoBase F G₁ G₂ M M)) =>
    Q.size (rep.ty (evalStateTy value)) p.1 ≤ width ∧ cacheOK p.2
  have hret := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy value)) effect selectRow pre middle saved (5 * width) selectTime
    (by intro e he; subst e; exact henv.trans h5)
    (by intro c hc; subst c; exact hs.trans h5)
    (by intro e he; subst e; exact ⟨rfl, hrow.trans h5⟩)
    (by intro e he; subst e; exact ht)
  have hquery := Language.query_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy value)) effect EvalCmd.lookup (.fst (.fst v0))
    (fun e => middle e.1 ∧ pre e.2) (fun m => m = row.1.1) saved
    (fun p => answerOK p.1 ∧ cacheOK p.2) (5 * width) (5 * fee) readTime (hh.trans h5)
    (by rintro ⟨r, e⟩ ⟨rfl, rfl⟩; exact hrowEnv.trans (by omega))
    (by intro c hc; subst c; exact hs.trans h5)
    (by rintro ⟨r, e⟩ ⟨rfl, rfl⟩; exact ⟨rfl, hkeySize.trans h5⟩)
    (by rintro ⟨r, e⟩ ⟨rfl, rfl⟩; exact hkey.trans (by omega))
    (by
      intro input hinput z hz
      have heq : input = (row.1.1, cache) := Prod.ext hinput.1 hinput.2
      rw [heq] at hz
      exact hread z hz)
  have hfinish := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy value)) effect (evalUpdate combine)
    (fun e => answerOK e.1 ∧ middle e.2.1 ∧ pre e.2.2)
    (fun a => Q.size (rep.ty (evalStateTy value)) a ≤ width) cacheOK (5 * width) updateTime
    (by rintro ⟨a, r, e⟩ ⟨ha, rfl, rfl⟩; exact hupdateEnv a ha)
    (by intro c hc; exact hc.trans h5)
    (by rintro ⟨a, r, e⟩ ⟨ha, rfl, rfl⟩; exact ⟨hresult a ha, (hresult a ha).trans h5⟩)
    (by rintro ⟨a, r, e⟩ ⟨ha, rfl, rfl⟩; exact hupdate a ha)
  have hinner := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing
    rep data P primitive (rep.ty (cacheTy value)) effect (.query .lookup (.fst (.fst v0))) (.ret (evalUpdate combine))
    (fun e => middle e.1 ∧ pre e.2) answerOK saved cacheOK finalOK (5 * width)
    (5 * fee + readTime + 3 * fee) (updateTime + 2 * fee) (hh.trans h5)
    (by rintro ⟨r, e⟩ ⟨rfl, rfl⟩; exact hrowEnv.trans (by omega))
    (by intro a ha; exact ha.trans h5)
    (by intro c hc; subst c; exact hs.trans h5)
    (by intro c hc; exact hc.trans h5) hquery hfinish
  have houter := Language.bind_bound_of_width sizes laws mono control queryCost routing
    rep data P primitive (rep.ty (cacheTy value)) effect (.ret selectRow)
    (.bind (.query .lookup (.fst (.fst v0))) (.ret (evalUpdate combine)))
    pre middle saved finalOK (5 * width) (selectTime + 2 * fee)
    ((5 * fee + readTime + 3 * fee) + (updateTime + 2 * fee) + 20 * fee) (hh.trans h5)
    (by intro e he; subst e; exact henv.trans h5)
    (by intro r hr'; subst r; exact hrow.trans h5)
    (by intro c hc; subst c; exact hs.trans h5) hret hinner
  have h := houter (env, cache) ⟨rfl, rfl⟩ out hout
  have hfee : fee ≤ overhead (256 * width) := mono (by omega)
  exact ⟨h.1, by dsimp only [fee] at h ⊢; omega⟩

end Signatures.Runtime.LazyAGM
