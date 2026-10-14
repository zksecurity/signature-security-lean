import Signatures.Runtime.BackendLanguageCost
import Signatures.Runtime.BackendCallerRouting

/-! Compositional budgets for compiled stateful wrapper programs. Local context
copying, native invocation, sequencing, and branch dispatch are all charged in
encoded widths. These rules do not inherit the old arithmetic step counts. -/

open OracleComp OracleSpec PFunctor

namespace Signatures.Runtime.BackendProgram.Language

universe v w

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [QP : Q.HasProd] [QS : Q.HasSum]
  {I S : Type} {spec : OracleSpec I} {iface : Interface (C := C) spec}
  {header : Nat} (sizes : SizeLaws Q header)
  {overhead : Nat → Nat} (laws : LocalCostLaws Q overhead) (mono : Monotone overhead)
  (control : ControlCosts) (queryCost : (i : I) → spec.Range i → Nat)
  (routing : RoutingCostLaws control overhead)

include sizes laws mono

theorem contextInput_cost_of_width {A E : Type} (a : C.Str A) (e : C.Str E)
    (store : C.Str S) {f : A → E} (context : Q.Realizer a e f)
    (input : A × S) (width contextTime : Nat) (hh : header ≤ width)
    (ha : Q.size a input.1 ≤ width) (hs : Q.size store input.2 ≤ width)
    (he : Q.size e (f input.1) ≤ width) (ht : Q.cost context input.1 ≤ contextTime) :
    Q.cost (contextInput a e store context) input ≤ contextTime + 4 * overhead (32 * width) := by
  have hp := sizes.prod_le a store input
  have ho := sizes.prod_le (StepClass.HasProd.prod a store) e (input, f input.1)
  refine ((contextInputBound laws a e store (LocalBound.measured context)).cost_le input).trans ?_
  dsimp only [contextInputBound, LocalBound.measured, LocalBound.pair, LocalBound.compose,
    LocalBound.fst, LocalBound.identity]
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  grind only

theorem contextReturn_cost_of_width {B E : Type} (b : C.Str B) (e : C.Str E)
    (store : C.Str S) (value : B) (saved : S) (context : E) (width : Nat)
    (hh : header ≤ width) (hb : Q.size b value ≤ width)
    (hs : Q.size store saved ≤ width) (he : Q.size e context ≤ width) :
    Q.cost (contextReturn (Q := Q) b e store) ((value, saved), context) ≤
      9 * overhead (32 * width) := by
  have hp := sizes.prod_le b store (value, saved)
  have hi := sizes.prod_le (StepClass.HasProd.prod b store) e ((value, saved), context)
  have hc := sizes.prod_le b e (value, context)
  have ho := sizes.prod_le (StepClass.HasProd.prod b e) store ((value, context), saved)
  refine ((contextReturnBound laws b e store).cost_le ((value, saved), context)).trans ?_
  dsimp only [contextReturnBound, LocalBound.pair, LocalBound.compose, LocalBound.fst, LocalBound.snd]
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  grind only

include routing

/-- Retain a bounded local environment across a stateful body. The output
predicate retains both the body's invariant and the saved environment predicate. -/
theorem withContext_bound_of_width {A B E : Type} {a : C.Str A} {b : C.Str B} {e : C.Str E}
    (store : C.Str S) {f : A → E} (context : Q.Realizer a e f)
    (body : Code Q spec iface (StepClass.HasProd.prod a store) (StepClass.HasProd.prod b store))
    (pre : A × S → Prop) (post : B × S → Prop) (keep : E → Prop)
    (width contextTime bodyTime : Nat) (hh : header ≤ width)
    (hi : ∀ p, pre p → Q.size a p.1 ≤ width ∧ Q.size store p.2 ≤ width ∧
      Q.size e (f p.1) ≤ width ∧ keep (f p.1) ∧ Q.cost context p.1 ≤ contextTime)
    (ho : ∀ p, post p → Q.size b p.1 ≤ width ∧ Q.size store p.2 ≤ width)
    (hb : Bounds control queryCost body pre post bodyTime) :
    Bounds control queryCost (withContext store context body) pre
      (fun p => post (p.1.1, p.2) ∧ keep p.1.2)
      (bodyTime + contextTime + 18 * overhead (32 * width)) := by
  intro input hp z hz
  simp only [withContext, Code.run, sequenceRun, retainRun, pure_bind, bind_map_left,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨mid, hmid, rfl⟩ := hz
  obtain ⟨r, hr, rfl⟩ := hmid
  obtain ⟨hout, ht⟩ := hb input hp r hr
  obtain ⟨ha, hs, he, hk, hc⟩ := hi input hp
  obtain ⟨hb', hs'⟩ := ho r.value hout
  refine ⟨⟨hout, hk⟩, ?_⟩
  have hin := contextInput_cost_of_width sizes laws mono a e store context input width contextTime hh ha hs he hc
  have hret := contextReturn_cost_of_width sizes laws mono b e store r.value.1 r.value.2 (f input.1)
    width hh hb' hs' he
  have hprod := @sizes.prod_le
  have hcall := routing.localCall
  have hseq := routing.sequence
  have hretain := routing.retain
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only at *
  grind only

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  (rep : LanguageRepresentation C base) (data : DataCode Q rep.data)
  (P : Primitives base Op)
  (primitive : {a b : Ty Atom} → (instr : Op a b) →
    Q.Realizer (rep.ty a) (rep.ty b) (P.execute instr))
  (store : C.Str S)
  (effect : {a b : Ty Atom} → Cmd a b →
    Code Q spec iface (StepClass.HasProd.prod (rep.ty a) store)
      (StepClass.HasProd.prod (rep.ty b) store))

omit sizes laws [C.HasOption] in
theorem ret_bound_of_width {Γ a} (expression : Expr Op Γ a)
    (pre : Env base Γ → Prop) (post : a.Value base → Prop) (inv : S → Prop)
    (width expressionTime : Nat)
    (hi : ∀ env, pre env → Q.size (rep.env Γ) env ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (ho : ∀ env, pre env → post (expression.denote P env) ∧
      Q.size (rep.ty a) (expression.denote P env) ≤ width)
    (ht : ∀ env, pre env → Q.cost (Expression.compile rep data P primitive expression) env ≤ expressionTime) :
    Bounds control queryCost (compile rep data P primitive store effect (.ret expression))
      (fun p => pre p.1 ∧ inv p.2) (fun p => post p.1 ∧ inv p.2)
      (expressionTime + 2 * overhead (32 * width)) := by
  intro input hp z hz
  simp only [compile, Code.run, retainRun, map_pure, support_pure, Set.mem_singleton_iff] at hz
  subst z
  obtain ⟨hout, hw⟩ := ho input.1 hp.1
  have ht' := ht input.1 hp.1
  have hi' := hi input.1 hp.1
  have hs' := hs input.2 hp.2
  have hcall := routing.localCall
  have hretain := routing.retain
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  exact ⟨⟨hout, hp.2⟩, by dsimp; grind only⟩

theorem bind_bound_of_width_transition {Γ a b} (initial : Program Op Cmd Γ a)
    (following : Program Op Cmd (a :: Γ) b)
    (pre : Env base Γ → Prop) (middle : a.Value base → Prop) (inv nextInv : S → Prop)
    (post : b.Value base × S → Prop) (width initialTime followingTime : Nat)
    (hh : header ≤ width)
    (hi : ∀ env, pre env → Q.size (rep.env Γ) env ≤ width)
    (hm : ∀ value, middle value → Q.size (rep.ty a) value ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (hsNext : ∀ saved, nextInv saved → Q.size store saved ≤ width)
    (hb : Bounds control queryCost (compile rep data P primitive store effect initial)
      (fun p => pre p.1 ∧ inv p.2) (fun p => middle p.1 ∧ nextInv p.2) initialTime)
    (hf : Bounds control queryCost (compile rep data P primitive store effect following)
      (fun p => (middle p.1.1 ∧ pre p.1.2) ∧ nextInv p.2) post followingTime) :
    Bounds control queryCost (compile rep data P primitive store effect (.bind initial following))
      (fun p => pre p.1 ∧ inv p.2) post
      (initialTime + followingTime + 20 * overhead (32 * width)) := by
  have hc := withContext_bound_of_width sizes laws mono control queryCost routing store
    (Q.identity (rep.env Γ)) (compile rep data P primitive store effect initial)
    (fun p => pre p.1 ∧ inv p.2) (fun p => middle p.1 ∧ nextInv p.2) pre width
    (overhead (32 * width)) initialTime hh
    (by
      intro p hp
      exact ⟨hi p.1 hp.1, hs p.2 hp.2, hi p.1 hp.1, hp.1,
        (laws.identity _ _).trans (mono (by have := hi p.1 hp.1; omega))⟩)
    (by intro p hp; exact ⟨hm p.1 hp.1, hsNext p.2 hp.2⟩) hb
  intro input hp z hz
  simp only [compile, Code.run, sequenceRun, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, t, ht, rfl⟩ := hz
  obtain ⟨⟨hm', hs'⟩, hk⟩ := (hc input hp r hr).1
  obtain ⟨hout, htime⟩ := hf r.value ⟨⟨hm', hk⟩, hs'⟩ t ht
  have hc' := (hc input hp r hr).2
  have henv := hi input.1 hp.1
  have hstore := hs input.2 hp.2
  have hvalue := hm r.value.1.1 hm'
  have hkeep := hi r.value.1.2 hk
  have hstore' := hsNext r.value.2 hs'
  have hprod := @sizes.prod_le
  have hseq := routing.sequence
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  refine ⟨hout, ?_⟩
  dsimp only [LanguageRepresentation.env] at *
  grind only

theorem bind_bound_of_width {Γ a b} (initial : Program Op Cmd Γ a)
    (following : Program Op Cmd (a :: Γ) b)
    (pre : Env base Γ → Prop) (middle : a.Value base → Prop) (inv : S → Prop)
    (post : b.Value base × S → Prop) (width initialTime followingTime : Nat)
    (hh : header ≤ width)
    (hi : ∀ env, pre env → Q.size (rep.env Γ) env ≤ width)
    (hm : ∀ value, middle value → Q.size (rep.ty a) value ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (hb : Bounds control queryCost (compile rep data P primitive store effect initial)
      (fun p => pre p.1 ∧ inv p.2) (fun p => middle p.1 ∧ inv p.2) initialTime)
    (hf : Bounds control queryCost (compile rep data P primitive store effect following)
      (fun p => (middle p.1.1 ∧ pre p.1.2) ∧ inv p.2) post followingTime) :
    Bounds control queryCost (compile rep data P primitive store effect (.bind initial following))
      (fun p => pre p.1 ∧ inv p.2) post
      (initialTime + followingTime + 20 * overhead (32 * width)) :=
  bind_bound_of_width_transition sizes laws mono control queryCost routing rep data P primitive
    store effect initial following pre middle inv inv post width initialTime followingTime
    hh hi hm hs hs hb hf

omit laws in
theorem query_bound_of_width {Γ a b} (instr : Cmd a b) (arg : Expr Op Γ a)
    (pre : Env base Γ → Prop) (argument : a.Value base → Prop) (inv : S → Prop)
    (post : b.Value base × S → Prop) (width argumentTime effectTime : Nat) (hh : header ≤ width)
    (hi : ∀ env, pre env → Q.size (rep.env Γ) env ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (ho : ∀ env, pre env → argument (arg.denote P env) ∧ Q.size (rep.ty a) (arg.denote P env) ≤ width)
    (ht : ∀ env, pre env → Q.cost (Expression.compile rep data P primitive arg) env ≤ argumentTime)
    (he : Bounds control queryCost (effect instr) (fun p => argument p.1 ∧ inv p.2) post effectTime) :
    Bounds control queryCost (compile rep data P primitive store effect (.query instr arg))
      (fun p => pre p.1 ∧ inv p.2) post
      (argumentTime + effectTime + 3 * overhead (32 * width)) := by
  intro input hp z hz
  simp only [compile, Code.run, retainRun, sequenceRun, map_pure, pure_bind,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨ha, hw⟩ := ho input.1 hp.1
  obtain ⟨hout, htime⟩ := he _ ⟨ha, hp.2⟩ r hr
  have ht' := ht input.1 hp.1
  have hi' := hi input.1 hp.1
  have hs' := hs input.2 hp.2
  have hprod := @sizes.prod_le
  have hcall := routing.localCall
  have hretain := routing.retain
  have hseq := routing.sequence
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  exact ⟨hout, by dsimp; grind only⟩

omit laws in
theorem call_bound_of_width {Γ Δ a} (body : Program Op Cmd Δ a) (args : Args Op Γ Δ)
    (pre : Env base Γ → Prop) (argument : Env base Δ → Prop) (inv : S → Prop)
    (post : a.Value base × S → Prop) (width argumentTime bodyTime : Nat) (hh : header ≤ width)
    (hi : ∀ env, pre env → Q.size (rep.env Γ) env ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (ho : ∀ env, pre env → argument (args.denote P env) ∧ Q.size (rep.env Δ) (args.denote P env) ≤ width)
    (ht : ∀ env, pre env → Q.cost (Expression.arguments rep data P primitive args) env ≤ argumentTime)
    (he : Bounds control queryCost (compile rep data P primitive store effect body)
      (fun p => argument p.1 ∧ inv p.2) post bodyTime) :
    Bounds control queryCost (compile rep data P primitive store effect (.call body args))
      (fun p => pre p.1 ∧ inv p.2) post
      (argumentTime + bodyTime + 3 * overhead (32 * width)) := by
  intro input hp z hz
  simp only [compile, Code.run, retainRun, sequenceRun, map_pure, pure_bind,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨ha, hw⟩ := ho input.1 hp.1
  obtain ⟨hout, htime⟩ := he _ ⟨ha, hp.2⟩ r hr
  have ht' := ht input.1 hp.1
  have hi' := hi input.1 hp.1
  have hs' := hs input.2 hp.2
  have hprod := @sizes.prod_le
  have hcall := routing.localCall
  have hretain := routing.retain
  have hseq := routing.sequence
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  exact ⟨hout, by dsimp; grind only⟩

omit routing in
theorem choose_cost_of_width {Γ} (cond : Expr Op Γ .bool)
    (env : Env base Γ) (saved : S) (width conditionTime : Nat) (hh : header ≤ width)
    (hi : Q.size (rep.env Γ) env ≤ width) (hs : Q.size store saved ≤ width)
    (hb : Q.size rep.data.bool (cond.denote P env) ≤ width)
    (dataLaws : DataCostLaws rep.data data overhead)
    (ht : Q.cost (Expression.compile rep data P primitive cond) env ≤ conditionTime) :
    Q.cost (choose rep data P primitive store cond) (env, saved) ≤
      conditionTime + 6 * overhead (32 * width) := by
  have hp := sizes.prod_le (rep.env Γ) store (env, saved)
  have hb' := sizes.prod_le rep.data.bool (StepClass.HasProd.prod (rep.env Γ) store)
    (cond.denote P env, (env, saved))
  have hsum := sizes.sum_le (StepClass.HasProd.prod (rep.env Γ) store)
    (StepClass.HasProd.prod (rep.env Γ) store)
    (if cond.denote P env = true then Sum.inl (env, saved) else Sum.inr (env, saved))
  have hfst := laws.fst (rep.env Γ) store (env, saved)
  have hcomp := laws.compose (QP.fst (rep.env Γ) store)
    (Expression.compile rep data P primitive cond) (env, saved)
  have hid := laws.identity (StepClass.HasProd.prod (rep.env Γ) store) (env, saved)
  have hpair := laws.pair
    (Q.compose (QP.fst (rep.env Γ) store) (Expression.compile rep data P primitive cond))
    (Q.identity (StepClass.HasProd.prod (rep.env Γ) store)) (env, saved)
  have hselect := dataLaws.select (StepClass.HasProd.prod (rep.env Γ) store)
    (cond.denote P env, (env, saved))
  have hlast := laws.compose
    (QP.pair (Q.compose (QP.fst (rep.env Γ) store) (Expression.compile rep data P primitive cond))
      (Q.identity (StepClass.HasProd.prod (rep.env Γ) store)))
    (data.select (StepClass.HasProd.prod (rep.env Γ) store)) (env, saved)
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  dsimp only [choose, LanguageRepresentation.ty, Function.comp_def, id] at *
  split_ifs at * <;> dsimp only [Sum.elim] at * <;> grind only

theorem branch_bound_of_width {Γ a} (cond : Expr Op Γ .bool)
    (yes no : Program Op Cmd Γ a) (pre : Env base Γ → Prop) (inv : S → Prop)
    (post : a.Value base × S → Prop) (width conditionTime yesTime noTime : Nat)
    (hh : header ≤ width) (hi : ∀ env, pre env → Q.size (rep.env Γ) env ≤ width)
    (hs : ∀ saved, inv saved → Q.size store saved ≤ width)
    (hb : ∀ b, Q.size rep.data.bool b ≤ width)
    (dataLaws : DataCostLaws rep.data data overhead)
    (ht : ∀ env, pre env → Q.cost (Expression.compile rep data P primitive cond) env ≤ conditionTime)
    (hy : Bounds control queryCost (compile rep data P primitive store effect yes)
      (fun p => (pre p.1 ∧ cond.denote P p.1 = true) ∧ inv p.2) post yesTime)
    (hn : Bounds control queryCost (compile rep data P primitive store effect no)
      (fun p => (pre p.1 ∧ cond.denote P p.1 ≠ true) ∧ inv p.2) post noTime) :
    Bounds control queryCost (compile rep data P primitive store effect (.branch cond yes no))
      (fun p => pre p.1 ∧ inv p.2) post
      (conditionTime + max yesTime noTime + 9 * overhead (32 * width)) := by
  intro input hp z hz
  have hc := choose_cost_of_width sizes laws mono rep data P primitive store cond input.1 input.2 width
    conditionTime hh (hi input.1 hp.1) (hs input.2 hp.2) (hb _) dataLaws (ht input.1 hp.1)
  have henv := hi input.1 hp.1
  have hstore := hs input.2 hp.2
  have hprod := @sizes.prod_le
  have hleft := sizes.sum_le (StepClass.HasProd.prod (rep.env Γ) store)
    (StepClass.HasProd.prod (rep.env Γ) store) (Sum.inl input)
  have hright := sizes.sum_le (StepClass.HasProd.prod (rep.env Γ) store)
    (StepClass.HasProd.prod (rep.env Γ) store) (Sum.inr input)
  dsimp only [Sum.elim] at hleft hright
  have hcall := routing.localCall
  have hbranch := routing.branch
  have hseq := routing.sequence
  have hfee : ∀ n ≤ 32 * width, overhead n ≤ overhead (32 * width) := fun _ hn => mono hn
  have hym := Nat.le_max_left yesTime noTime
  have hnm := Nat.le_max_right yesTime noTime
  by_cases hcond : cond.denote P input.1 = true
  · simp only [compile, Code.run, sequenceRun, pure_bind, hcond, ite_true, chargeRun,
      bind_map_left, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    obtain ⟨hout, htime⟩ := hy input ⟨⟨hp.1, hcond⟩, hp.2⟩ r hr
    exact ⟨hout, by dsimp; grind only⟩
  · simp only [compile, Code.run, sequenceRun, pure_bind, hcond, chargeRun,
      bind_map_left, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    obtain ⟨hout, htime⟩ := hn input ⟨⟨hp.1, hcond⟩, hp.2⟩ r hr
    exact ⟨hout, by dsimp; grind only⟩

end Signatures.Runtime.BackendProgram.Language
