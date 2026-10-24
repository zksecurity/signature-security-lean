import Proofs.Runtime.BackendWeightedEvaluate
import Proofs.Runtime.BackendLanguageIteration

/-! Resource assembly for the actual effectful evaluator. A remaining-indexed
body certificate is composed with count computation, initialization, loop
control, retained contexts, and the final accumulator projection. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.WeightedAGM.Evaluate

open BackendProgram Read LazyAGM.ReplySyntax

variable {indexTy : Ty CryptoAtom}

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {F G₁ G₂ K M : Type} [Field F]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] [DecidableEq K] [DecidableEq M]
  {iface : Interface (C := C) unifSpec}
  (rep : LanguageRepresentation C (cryptoBase F G₁ G₂ K M))
  (data : DataCode Q rep.data) (cost : PrimitiveCosts)
  (primitive : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) →
    Q.Realizer (rep.ty a) (rep.ty b) ((arithmetic F G₁ G₂ K M cost).execute instr))
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead)
  (dataLaws : DataCostLaws rep.data data overhead)
  (primitiveBound : {a b : Ty CryptoAtom} → (instr : CryptoOp a b) → LocalBound (primitive instr))
  {header : Nat} (sizes : SizeLaws Q header) (mono : Monotone overhead)

include laws dataLaws primitiveBound sizes mono

theorem evaluateInit_cost {value : Ty CryptoAtom}
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), (evalRowTy indexTy)] value)
    (env : Env (cryptoBase F G₁ G₂ K M) [.list (evalRowTy indexTy), (evalRowTy indexTy)])
    (width zeroTime : Nat) (hh : header ≤ width)
    (hu : Q.size rep.data.unit () ≤ width) (hn : Q.size rep.data.nat 0 ≤ width)
    (hi : Q.size (rep.env [.list (evalRowTy indexTy), (evalRowTy indexTy)]) env ≤ width)
    (hz : Q.size (rep.ty value) (zero.denote (arithmetic F G₁ G₂ K M cost) env) ≤ width)
    (ht : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive zero) env ≤ zeroTime) :
    Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (.pair (.nat 0) zero)) env ≤
      zeroTime + 8 * overhead (128 * width) := by
  have hnTime := Expression.cost_compile_le rep data (arithmetic F G₁ G₂ K M cost) primitive
    laws dataLaws primitiveBound (.nat 0 : Expr CryptoOp [.list (evalRowTy indexTy), (evalRowTy indexTy)] .nat) env
  have hp := laws.pair
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive (.nat 0))
    (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive zero) env
  have hprod := @sizes.prod_le
  have hfee : ∀ k ≤ 128 * width, overhead k ≤ overhead (128 * width) := fun _ hk => mono hk
  dsimp only [Expression.compile, Expression.compileBound, DataCostLaws.natBound,
    DataCostLaws.unitBound, LocalBound.compose, Expr.denote, LanguageRepresentation.ty] at hnTime hp ⊢
  grind only

variable (control : ControlCosts) (queryCost : (i : Nat) → unifSpec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include routing

theorem backendEvaluate_bound {value : Ty CryptoAtom}
    (reader : Code Q unifSpec iface (rep.ty (inputTy indexTy value))
      (rep.ty (.pair value (cacheTy indexTy value))))
    (zero : Expr CryptoOp [.list (evalRowTy indexTy), (evalRowTy indexTy)] value)
    (combine : Expr CryptoOp [value, scalar, value] value)
    (rows : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × F)) (default : indexTy.Value (cryptoBase F G₁ G₂ K M) × F)
    (cache : List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)))
    (inv : Nat → (Nat × value.Value (cryptoBase F G₁ G₂ K M)) ×
      List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)) → Prop)
    (width cap countTime initTime bodyTime tickTime : Nat)
    (hh : header ≤ width)
    (henv : Q.size (rep.env [.list (evalRowTy indexTy), (evalRowTy indexTy)]) (rows, default, ()) ≤ width)
    (hn : ∀ n ≤ cap, Q.size rep.data.nat n ≤ width)
    (hcap : rows.length ≤ cap)
    (hi : inv rows.length ((0, zero.denote (arithmetic F G₁ G₂ K M cost) (rows, default, ())), cache))
    (hsize : ∀ remaining ≤ cap, ∀ p, inv remaining p →
      Q.size (rep.ty (evalStateTy value)) p.1 ≤ width ∧ Q.size (rep.ty (cacheTy indexTy value)) p.2 ≤ width)
    (hcount : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (listLength (cell := (evalRowTy indexTy)) (Γ := [(evalRowTy indexTy)]) CryptoOp.natAdd)) (rows, default, ()) ≤ countTime)
    (hinit : Q.cost (Expression.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
      (.pair (.nat 0) zero)) (rows, default, ()) ≤ initTime)
    (hbody : ∀ remaining < cap, ∀ acc saved, inv (remaining + 1) (acc, saved) →
      ∀ out ∈ support ((Language.compile rep data (arithmetic F G₁ G₂ K M cost) primitive
        (rep.ty (cacheTy indexTy value)) (readEffect rep reader)
        (evalBody combine)).run control queryCost ((acc, rows, default, ()), saved)),
        inv remaining out.value ∧ out.steps ≤ bodyTime)
    (htick : ∀ n ≤ cap, ∀ encoded ≤ 7 * width, control.loop n encoded ≤ tickTime)
    (out : Run (value.Value (cryptoBase F G₁ G₂ K M) × List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M))))
    (hout : out ∈ support ((backendEvaluate rep data cost primitive reader zero combine).run
      control queryCost ((rows, default, ()), cache))) :
    (Q.size (rep.ty value) out.value.1 ≤ width ∧ Q.size (rep.ty (cacheTy indexTy value)) out.value.2 ≤ width) ∧
      out.steps ≤ countTime + initTime + cap * (bodyTime + 19 * overhead (128 * width) + tickTime) +
        tickTime + 64 * overhead (128 * width) := by
  let P := arithmetic F G₁ G₂ K M cost
  let env : Env (cryptoBase F G₁ G₂ K M) [.list (evalRowTy indexTy), (evalRowTy indexTy)] := (rows, default, ())
  let effect : {a b : Ty CryptoAtom} → EvalCmd indexTy value a b →
      Code Q unifSpec iface (StepClass.HasProd.prod (rep.ty a) (rep.ty (cacheTy indexTy value)))
        (StepClass.HasProd.prod (rep.ty b) (rep.ty (cacheTy indexTy value))) :=
    readEffect rep reader
  let count : Expr CryptoOp [.list (evalRowTy indexTy), (evalRowTy indexTy)] .nat := listLength CryptoOp.natAdd
  let init : Expr CryptoOp [.list (evalRowTy indexTy), (evalRowTy indexTy)] (evalStateTy value) := .pair (.nat 0) zero
  let fee := overhead (128 * width)
  let loopTime := countTime + initTime + cap * (bodyTime + 19 * fee + tickTime) + tickTime + 32 * fee
  have hlen : count.denote P env = rows.length :=
    listLength_denote (cell := (evalRowTy indexTy)) (Γ := [(evalRowTy indexTy)]) P CryptoOp.natAdd (fun _ _ => rfl) rows (default, ())
  have hloop := Language.loop_bound_remaining sizes laws mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy indexTy value)) effect count init (evalBody combine) env cache inv
    width cap countTime initTime bodyTime tickTime hh henv hn (by simpa only [hlen] using hcap)
    (by simpa only [hlen, init, Expr.denote] using hi) hsize hcount hinit hbody htick
  obtain ⟨_, hcache⟩ := hsize rows.length hcap _ hi
  have h3 : width ≤ 3 * width := by omega
  let pre := fun e => e = env
  let middle := fun a => Q.size (rep.ty (evalStateTy value)) a ≤ width
  let saved := fun c => c = cache
  let nextSaved := fun c => Q.size (rep.ty (cacheTy indexTy value)) c ≤ width
  let post := fun p : value.Value (cryptoBase F G₁ G₂ K M) × List (indexTy.Value (cryptoBase F G₁ G₂ K M) × value.Value (cryptoBase F G₁ G₂ K M)) =>
    Q.size (rep.ty value) p.1 ≤ width ∧ nextSaved p.2
  have hbodyBound : Bounds control queryCost
      (Language.compile rep data P primitive (rep.ty (cacheTy indexTy value)) effect (.loop count init (evalBody combine)))
      (fun p => pre p.1 ∧ saved p.2) (fun p => middle p.1 ∧ nextSaved p.2) loopTime := by
    intro input hp z hz
    have heq : input = (env, cache) := Prod.ext hp.1 hp.2
    rw [heq] at hz
    have h := hloop z hz
    exact ⟨hsize 0 (Nat.zero_le cap) _ h.1, h.2⟩
  have hfinish := Language.ret_bound_of_width mono control queryCost routing rep data P primitive
    (rep.ty (cacheTy indexTy value)) effect (.snd v0)
    (fun e => middle e.1 ∧ pre e.2) (fun a => Q.size (rep.ty value) a ≤ width) nextSaved
    (3 * width) (3 * fee)
    (by
      rintro ⟨a, e⟩ ⟨ha, rfl⟩
      have hp := sizes.prod_le (rep.ty (evalStateTy value)) (rep.env [.list (evalRowTy indexTy), (evalRowTy indexTy)]) (a, env)
      change Q.size (rep.env [evalStateTy value, .list (evalRowTy indexTy), (evalRowTy indexTy)]) (a, env) ≤ _ at hp
      dsimp only at hp
      change Q.size (rep.ty (evalStateTy value)) a ≤ width at ha
      have he : Q.size (rep.env [.list (evalRowTy indexTy), (evalRowTy indexTy)]) env ≤ width := henv
      exact hp.trans (by omega))
    (by intro c hc; exact hc.trans h3)
    (by
      rintro ⟨a, e⟩ ⟨ha, rfl⟩
      have h := (sizes.snd_le rep.data.nat (rep.ty value) a).trans ha
      exact ⟨h, h.trans h3⟩)
    (by
      rintro ⟨a, e⟩ ⟨ha, rfl⟩
      apply (Expression.cost_compile_le rep data P primitive laws dataLaws primitiveBound _ _).trans
      have hprod := @sizes.prod_le
      have hfst := @sizes.fst_le
      have hsnd := @sizes.snd_le
      have hfee : ∀ k ≤ 128 * width, overhead k ≤ fee := fun _ hk => mono hk
      dsimp only [Expression.compileBound, Expression.variableBound, v0, LocalBound.compose,
        LocalBound.fst, LocalBound.snd, Expr.denote, Var.get, middle, pre,
        LanguageRepresentation.env, LanguageRepresentation.ty] at *
      grind only)
  have hbound := Language.bind_bound_of_width_transition sizes laws mono control queryCost routing
    rep data P primitive (rep.ty (cacheTy indexTy value)) effect (.loop count init (evalBody combine)) (.ret (.snd v0))
    pre middle saved nextSaved post (3 * width) loopTime
    (3 * fee + 2 * overhead (32 * (3 * width))) (hh.trans h3)
    (by intro e he; subst e; exact henv.trans h3)
    (by intro a ha; exact ha.trans h3)
    (by intro c hc; subst c; exact hcache.trans h3)
    (by intro c hc; exact hc.trans h3) hbodyBound hfinish
  rw [backendEvaluate] at hout
  have h := hbound (env, cache) ⟨rfl, rfl⟩ out hout
  have hfee : overhead (32 * (3 * width)) ≤ fee := mono (by omega)
  exact ⟨h.1, by dsimp only [loopTime, fee] at *; omega⟩

end Signatures.Runtime.WeightedAGM.Evaluate
