import Signatures.Runtime.BackendWeightedEvaluate
import Signatures.Runtime.BackendLanguageBudget

/-! Composition of one implemented evaluator iteration. Selection, private
access, and arithmetic costs are joined with the native compiler's context,
query-argument, retention, invocation, and sequencing costs. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Evaluate

open BackendProgram Read LazyAGM.ReplySyntax

variable {indexTy : Ty CryptoAtom}

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include sizes mono laws dataLaws primitiveBound

theorem evalKey_cost {Γ : List (Ty CryptoAtom)}
    (env : Env (cryptoBase F G₁ G₂ K M) ((evalRowTy indexTy) :: Γ)) (width : Nat)
    (hi : Q.size (rep.env ((evalRowTy indexTy) :: Γ)) env ≤ width) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (.fst (.var .here) : Expr CryptoOp ((evalRowTy indexTy) :: Γ) indexTy)) env ≤
        5 * overhead (16 * width) := by
  refine (Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
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
    (reader : Code Q unifSpec iface (rep.ty (inputTy indexTy value))
      (rep.ty (.pair value (cacheTy indexTy value))))
    (combine : Expr CryptoOp [value, scalar, value] value)
    (n : Nat) (acc : value.Value (cryptoBase F G₁ G₂ K M))
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (width selectTime readTime updateTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)])
      ((n, acc), rows, default, ()) ≤ width)
    (hs : Q.size (rep.ty (cacheTy indexTy value)) cache ≤ width)
    (hr : Q.size (rep.ty (evalRowTy indexTy))
      ((selectRow (value := value)).denote (arithmetic F G₁ G₂ K M cost)
        ((n, acc), rows, default, ())) ≤ width)
    (ht : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (selectRow (value := value))) ((n, acc), rows, default, ()) ≤ selectTime)
    (hread : ∀ z ∈ support ((reader).run control queryCost
        (((selectRow (value := value)).denote (arithmetic F G₁ G₂ K M cost)
          ((n, acc), rows, default, ())).1, cache)),
      (Q.size (rep.ty value) z.value.1 ≤ width ∧ Q.size (rep.ty (cacheTy indexTy value)) z.value.2 ≤ width) ∧
        z.steps ≤ readTime)
    (hupdate : ∀ answer, Q.size (rep.ty value) answer ≤ width →
      Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (evalUpdate combine))
        (answer, (selectRow (value := value)).denote (arithmetic F G₁ G₂ K M cost)
          ((n, acc), rows, default, ()), (n, acc), rows, default, ()) ≤ updateTime)
    (hresult : ∀ answer, Q.size (rep.ty value) answer ≤ width →
      Q.size (rep.ty (evalStateTy value))
        ((evalUpdate combine).denote (arithmetic F G₁ G₂ K M cost)
          (answer, (selectRow (value := value)).denote (arithmetic F G₁ G₂ K M cost)
            ((n, acc), rows, default, ()), (n, acc), rows, default, ())) ≤ width)
    (out : Run ((Nat × value.Value (cryptoBase F G₁ G₂ K M)) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (rep.ty (cacheTy indexTy value)) (readEffect rep reader)
      (evalBody combine)).run control queryCost (((n, acc), rows, default, ()), cache))) :
    (Q.size (rep.ty (evalStateTy value)) out.value.1 ≤ width ∧
      Q.size (rep.ty (cacheTy indexTy value)) out.value.2 ≤ width) ∧
      out.steps ≤ selectTime + readTime + updateTime + 64 * overhead (256 * width) := by
  let P := arithmetic F G₁ G₂ K M cost
  let effect : {a b : Ty CryptoAtom} → EvalCmd indexTy value a b →
      Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty (cacheTy indexTy value)))
        (StepClass.HasProd.prod (rep.ty b) (rep.ty (cacheTy indexTy value))) :=
    readEffect rep reader
  let env : Env (cryptoBase F G₁ G₂ K M) [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)] :=
    ((n, acc), rows, default, ())
  let row := (selectRow (value := value)).denote P env
  let fee := overhead (32 * (5 * width))
  have h5 : width ≤ 5 * width := by omega
  have hprod := @sizes.prod_le
  have hfst := @sizes.fst_le
  have hsnd := @sizes.snd_le
  have hrow : Q.size (rep.ty (evalRowTy indexTy)) row ≤ width := hr
  have henv : Q.size (rep.env [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)]) env ≤ width := hi
  have hrowEnv : Q.size (rep.env [(evalRowTy indexTy), evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)])
      (row, env) ≤ 3 * width := by
    have h := sizes.prod_le (rep.ty (evalRowTy indexTy)) (rep.env [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)]) (row, env)
    dsimp only at h
    exact h.trans (by omega)
  have hupdateEnv (answer : value.Value (cryptoBase F G₁ G₂ K M))
      (ha : Q.size (rep.ty value) answer ≤ width) :
      Q.size (rep.env [value, (evalRowTy indexTy), evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)])
        (answer, row, env) ≤ 5 * width := by
    have h := sizes.prod_le (rep.ty value)
      (rep.env [(evalRowTy indexTy), evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)]) (answer, row, env)
    dsimp only at h
    exact h.trans (by omega)
  have hkeySize : Q.size (rep.ty indexTy) row.1 ≤ width := by
    dsimp only [evalRowTy, LanguageRepresentation.ty] at *
    grind only
  have hkey := evalKey_cost rep data cost primitive laws dataLaws primitiveBound sizes mono
    (row, env) (3 * width) hrowEnv
  have hkeyFee : overhead (16 * (3 * width)) ≤ fee := mono (by omega)
  let pre := fun e => e = env
  let middle := fun r => r = row
  let saved := fun c => c = cache
  let answerOK := fun a => Q.size (rep.ty value) a ≤ width
  let cacheOK := fun c => Q.size (rep.ty (cacheTy indexTy value)) c ≤ width
  let finalOK := fun p : (Nat × value.Value (cryptoBase F G₁ G₂ K M)) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)) =>
    Q.size (rep.ty (evalStateTy value)) p.1 ≤ width ∧ cacheOK p.2
  have hret := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy indexTy value)) effect selectRow pre middle saved (5 * width) selectTime
    (by intro e he; subst e; exact henv.trans h5)
    (by intro c hc; subst c; exact hs.trans h5)
    (by intro e he; subst e; exact ⟨rfl, hrow.trans h5⟩)
    (by intro e he; subst e; exact ht)
  have hquery := Language.query_bound_of_width sizes mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy indexTy value)) effect EvalCmd.lookup (.fst v0)
    (fun e => middle e.1 ∧ pre e.2) (fun m => m = row.1) saved
    (fun p => answerOK p.1 ∧ cacheOK p.2) (5 * width) (5 * fee) readTime (hh.trans h5)
    (by rintro ⟨r, e⟩ ⟨rfl, rfl⟩; exact hrowEnv.trans (by omega))
    (by intro c hc; subst c; exact hs.trans h5)
    (by rintro ⟨r, e⟩ ⟨rfl, rfl⟩; exact ⟨rfl, hkeySize.trans h5⟩)
    (by rintro ⟨r, e⟩ ⟨rfl, rfl⟩; exact hkey.trans (by omega))
    (by
      intro input hinput z hz
      have heq : input = (row.1, cache) := Prod.ext hinput.1 hinput.2
      rw [heq] at hz
      exact hread z hz)
  have hfinish := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy indexTy value)) effect (evalUpdate combine)
    (fun e => answerOK e.1 ∧ middle e.2.1 ∧ pre e.2.2)
    (fun a => Q.size (rep.ty (evalStateTy value)) a ≤ width) cacheOK (5 * width) updateTime
    (by rintro ⟨a, r, e⟩ ⟨ha, rfl, rfl⟩; exact hupdateEnv a ha)
    (by intro c hc; exact hc.trans h5)
    (by rintro ⟨a, r, e⟩ ⟨ha, rfl, rfl⟩; exact ⟨hresult a ha, (hresult a ha).trans h5⟩)
    (by rintro ⟨a, r, e⟩ ⟨ha, rfl, rfl⟩; exact hupdate a ha)
  have hinner := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing
    rep data P primitive (rep.ty (cacheTy indexTy value)) effect (.query .lookup (.fst v0)) (.ret (evalUpdate combine))
    (fun e => middle e.1 ∧ pre e.2) answerOK saved cacheOK finalOK (5 * width)
    (5 * fee + readTime + 3 * fee) (updateTime + 2 * fee) (hh.trans h5)
    (by rintro ⟨r, e⟩ ⟨rfl, rfl⟩; exact hrowEnv.trans (by omega))
    (by intro a ha; exact ha.trans h5)
    (by intro c hc; subst c; exact hs.trans h5)
    (by intro c hc; exact hc.trans h5) hquery hfinish
  have houter := Language.bind_bound_of_width sizes laws mono control queryCost routing
    rep data P primitive (rep.ty (cacheTy indexTy value)) effect (.ret selectRow)
    (.bind (.query .lookup (.fst v0)) (.ret (evalUpdate combine)))
    pre middle saved finalOK (5 * width) (selectTime + 2 * fee)
    ((5 * fee + readTime + 3 * fee) + (updateTime + 2 * fee) + 20 * fee) (hh.trans h5)
    (by intro e he; subst e; exact henv.trans h5)
    (by intro r hr'; subst r; exact hrow.trans h5)
    (by intro c hc; subst c; exact hs.trans h5) hret hinner
  have h := houter (env, cache) ⟨rfl, rfl⟩ out hout
  have hfee : fee ≤ overhead (256 * width) := mono (by omega)
  exact ⟨h.1, by dsimp only [fee] at h ⊢; omega⟩

end Signatures.Runtime.WeightedAGM.Evaluate
