import Signatures.Runtime.Program
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! Weighted oracle paths connect source execution counters to the library's
structural query bounds. Replies are arbitrary, including adaptive paths. -/

namespace Signatures.Runtime

open OracleComp

variable {I A B : Type} {spec : OracleSpec.{0, 0} I}

inductive QueryCost (weight : spec.Domain → Nat) : OracleComp spec A → A → Nat → Prop
  | pure (a : A) : QueryCost weight (pure a) a 0
  | queryBind (q : spec.Domain) (next : spec.Range q → OracleComp spec A) (reply : spec.Range q)
      {out n} : QueryCost weight (next reply) out n →
      QueryCost weight (PFunctor.FreeM.liftBind q next) out (weight q+n)

namespace QueryCost

variable {weight : spec.Domain → Nat} {code : OracleComp spec A} {out : A} {n : Nat}

@[simp] theorem pure_iff (a : A) : QueryCost weight (Pure.pure a) out n ↔ a = out ∧ n = 0 := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .pure _

theorem queryBind_iff (q : spec.Domain) (next : spec.Range q → OracleComp spec A) :
    QueryCost weight (OracleComp.queryBind q next) out n ↔
      ∃ reply k, QueryCost weight (next reply) out k ∧ n = weight q + k := by
  constructor
  · intro h; cases h with
    | queryBind _ _ reply tail => exact ⟨reply, _, tail, rfl⟩
  · rintro ⟨reply, k, hk, rfl⟩; exact .queryBind q next reply hk

theorem mem_support (h : QueryCost weight code out n) : out ∈ support code := by
  induction h with
  | pure a => simp
  | queryBind q next reply h ih =>
    change _ ∈ support ((liftM (spec.query q) : OracleComp spec _) >>= next)
    simp only [mem_support_bind_iff]
    exact ⟨reply, mem_support_query q reply, ih⟩

theorem exists_of_support (weight : spec.Domain → Nat) (code : OracleComp spec A)
    (out : A) (h : out ∈ support code) : ∃ n, QueryCost weight code out n := by
  induction code using OracleComp.inductionOn with
  | pure a =>
    simp only [support_pure, Set.mem_singleton_iff] at h
    subst out
    exact ⟨0, .pure a⟩
  | query_bind q next ih =>
    obtain ⟨reply, _, h⟩ := support_bind_exists h
    obtain ⟨n, hn⟩ := ih reply h
    exact ⟨weight q+n, .queryBind q next reply hn⟩

theorem bind {next : A → OracleComp spec B} {result : B} {m : Nat}
    (h : QueryCost weight code out n) (ht : QueryCost weight (next out) result m) :
    QueryCost weight (code >>= next) result (n+m) := by
  induction h with
  | pure a => simpa only [pure_bind, Nat.zero_add] using ht
  | queryBind q step reply h ih =>
    change QueryCost weight (PFunctor.FreeM.liftBind q (fun x => step x >>= next)) result _
    simpa only [Nat.add_assoc] using QueryCost.queryBind q (fun x => step x >>= next) reply (ih ht)

theorem bind_iff (weight : spec.Domain → Nat) (code : OracleComp spec A)
    (next : A → OracleComp spec B) (result : B) (n : Nat) :
    QueryCost weight (code >>= next) result n ↔
      ∃ out k m, QueryCost weight code out k ∧ QueryCost weight (next out) result m ∧ n = k+m := by
  constructor
  · intro h
    induction code using OracleComp.inductionOn generalizing n with
    | pure a => exact ⟨a, 0, n, .pure a, by simpa only [pure_bind] using h, by omega⟩
    | query_bind q step ih =>
      rw [bind_assoc] at h
      change QueryCost weight (PFunctor.FreeM.liftBind q (fun x => step x >>= next)) result n at h
      cases h with
      | queryBind _ _ reply h =>
        obtain ⟨out, k, m, hk, hm, hn⟩ := ih reply _ h
        exact ⟨out, weight q+k, m, .queryBind q step reply hk, hm, by omega⟩
  · rintro ⟨out, k, m, hk, hm, rfl⟩
    exact hk.bind hm

theorem map_iff (weight : spec.Domain → Nat) (code : OracleComp spec A) (f : A → B) (b : B) (n : Nat) :
    QueryCost weight (f <$> code) b n ↔ ∃ a, QueryCost weight code a n ∧ f a = b := by
  rw [map_eq_bind_pure_comp, bind_iff]
  constructor
  · rintro ⟨a, k, m, hk, hm, hn⟩
    cases hm
    simp only [Nat.add_zero] at hn
    subst n
    exact ⟨a, hk, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, n, 0, ha, .pure _, by omega⟩

/-- A bound on every weighted path gives a structural, decreasing query budget.
Nonempty replies rule out vacuous bounds on a query with no terminal paths. -/
theorem isQueryBound [∀ q, Nonempty (spec.Range q)] (weight : spec.Domain → Nat)
    (code : OracleComp spec A) (B : Nat)
    (h : ∀ out n, QueryCost weight code out n → n ≤ B) :
    IsQueryBound code B (fun q left => weight q ≤ left) (fun q left => left-weight q) := by
  induction code using OracleComp.inductionOn generalizing B with
  | pure a => exact isQueryBound_pure _ _ _ _
  | query_bind q next ih =>
    rw [isQueryBound_query_bind_iff]
    constructor
    · obtain ⟨reply⟩ := (inferInstance : Nonempty (spec.Range q))
      obtain ⟨out, hout⟩ := support_nonempty (next reply)
      obtain ⟨n, hn⟩ := exists_of_support weight (next reply) out hout
      have := h out (weight q+n) (.queryBind q next reply hn)
      omega
    · intro reply
      apply ih reply
      intro out n hn
      have := h out (weight q+n) (.queryBind q next reply hn)
      omega

end QueryCost

variable {S : Type}

/-- Exact additive state accounting along semantic paths. -/
theorem repeatDenote_queryPotential (weight : spec.Domain → Nat) (potential : S → Nat)
    (step : A → StateT S (OracleComp spec) A)
    (hstep : ∀ x state out n, QueryCost weight ((step x).run state) out n →
      potential out.2 = potential state + n)
    (count : Nat) (x : A) (state : S) (out : A × S) (n : Nat)
    (h : QueryCost weight ((repeatDenote step count x).run state) out n) :
    potential out.2 = potential state + n := by
  induction count generalizing x state out n with
  | zero =>
      simp only [repeatDenote, StateT.run_pure] at h
      cases h
      simp
  | succ count ih =>
      rw [repeatDenote, StateT.run_bind] at h
      obtain ⟨first, k, m, hk, hm, rfl⟩ := (QueryCost.bind_iff _ _ _ _ _).1 h
      have hfirst := hstep x state first k hk
      have hrest := ih first.1 first.2 out m hm
      omega

theorem Program.denote_queryPotential {Atom : Type} {base : Atom → Type}
    {Op Cmd : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (weight : spec.Domain → Nat) (potential : S → Nat)
    (H : SemanticsM base Cmd (StateT S (OracleComp spec)))
    (hhandler : ∀ {a b} (cmd : Cmd a b) arg state out n,
      QueryCost weight ((H cmd arg).run state) out n → potential out.2 = potential state + n)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) (state : S)
    (out : a.Value base × S) (n : Nat)
    (h : QueryCost weight ((code.denote P H env).run state) out n) :
    potential out.2 = potential state + n := by
  induction code generalizing state n with
  | ret e => cases h; simp
  | query cmd arg => exact hhandler cmd _ state out n h
  | bind first next ih ihnext =>
      rw [Program.denote, StateT.run_bind] at h
      obtain ⟨mid, k, m, hk, hm, rfl⟩ := (QueryCost.bind_iff _ _ _ _ _).1 h
      have hfirst := ih env state mid k hk
      have hrest := ihnext (mid.1, env) mid.2 out m hm
      omega
  | branch cond yes no ihyes ihno =>
      simp only [Program.denote] at h
      split at h <;> first | exact ihyes env state out n h | exact ihno env state out n h
  | loop count init body ih =>
      exact repeatDenote_queryPotential weight potential _ (fun x s out n => ih (x, env) s out n)
        _ _ state out n h
  | call body args ih => exact ih (args.denote P env) state out n h

theorem repeatRun_queryCost (weight : spec.Domain → Nat)
    (step : A → StateT S (OracleComp spec) (Run A))
    (hstep : ∀ x state out n, QueryCost weight ((step x).run state) out n → n ≤ out.1.steps)
    (count : Nat) (x : A) (state : S) (out : Run A × S) (n : Nat)
    (h : QueryCost weight ((repeatRun step count x).run state) out n) : n ≤ out.1.steps := by
  induction count generalizing x state out n with
  | zero =>
    simp only [repeatRun, StateT.run_pure] at h
    cases h
    exact Nat.zero_le _
  | succ count ih =>
    simp only [repeatRun, StateT.run_bind, StateT.run_pure] at h
    obtain ⟨first, c₁, rest, hfirst, hrest, hn⟩ := (QueryCost.bind_iff _ _ _ _ _).mp h
    obtain ⟨last, c₂, final, hlast, hfinal, hn'⟩ := (QueryCost.bind_iff _ _ _ _ _).mp hrest
    cases hfinal
    have ha := hstep x state first c₁ hfirst
    have hb := ih first.1.value first.2 last c₂ hlast
    dsimp only
    omega

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}

/-- One extra unit per primitive handler is paid by the program's query
constructor. Thus even a zero-priced sampler consumes a positive query budget. -/
theorem Program.run_queryCost (P : Primitives base Op) (weight : spec.Domain → Nat)
    (H : HandlerM base Cmd (StateT S (OracleComp spec)))
    (hhandler : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base) state out n,
      QueryCost weight ((H cmd arg).run state) out n → n ≤ out.1.steps+1)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) (state : S)
    (out : Run (a.Value base) × S) (n : Nat)
    (h : QueryCost weight ((code.run P H env).run state) out n) : n ≤ out.1.steps := by
  induction code generalizing state n with
  | ret e =>
    simp only [run, StateT.run_pure] at h
    cases h
    exact Nat.zero_le _
  | query cmd arg =>
    simp only [run, StateT.run_bind, StateT.run_pure] at h
    obtain ⟨result, c, final, hc, hfinal, hn⟩ := (QueryCost.bind_iff _ _ _ _ _).mp h
    cases hfinal
    have hh := hhandler cmd (arg.run P env).value state result c hc
    dsimp only
    omega
  | bind first body ihfirst ihbody =>
    simp only [run, StateT.run_bind, StateT.run_pure] at h
    obtain ⟨first, c₁, rest, hfirst, hrest, hn⟩ := (QueryCost.bind_iff _ _ _ _ _).mp h
    obtain ⟨last, c₂, final, hlast, hfinal, hn'⟩ := (QueryCost.bind_iff _ _ _ _ _).mp hrest
    cases hfinal
    have ha := ihfirst env state first c₁ hfirst
    have hb := ihbody (first.1.value, env) first.2 last c₂ hlast
    dsimp only
    omega
  | branch cond yes no ihyes ihno =>
    by_cases hb : (cond.run P env).value = true
    · simp only [run, hb, ite_true, StateT.run_bind, StateT.run_pure] at h
      obtain ⟨result, c, final, hc, hfinal, hn⟩ := (QueryCost.bind_iff _ _ _ _ _).mp h
      cases hfinal
      have hh := ihyes env state result c hc
      dsimp only
      omega
    · simp only [run, hb] at h
      obtain ⟨result, c, final, hc, hfinal, hn⟩ := (QueryCost.bind_iff _ _ _ _ _).mp h
      cases hfinal
      have hh := ihno env state result c hc
      dsimp only
      omega
  | loop count init body ih =>
    simp only [run, StateT.run_bind, StateT.run_pure] at h
    obtain ⟨result, c, final, hc, hfinal, hn⟩ := (QueryCost.bind_iff _ _ _ _ _).mp h
    cases hfinal
    have hh := repeatRun_queryCost weight (fun x => body.run P H (x, env))
      (fun x => ih (x, env)) (count.run P env).value (init.run P env).value state result c hc
    dsimp only
    omega
  | call body args ih =>
    simp only [run, StateT.run_bind, StateT.run_pure] at h
    obtain ⟨result, c, final, hc, hfinal, hn⟩ := (QueryCost.bind_iff _ _ _ _ _).mp h
    cases hfinal
    have hh := ih (args.run P env).value state result c hc
    dsimp only
    omega

end Signatures.Runtime
