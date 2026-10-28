import VCVio.OracleComp.Coinductive.Machine

/-! # Implementation from a view-level simulation

A hand-built machine implements a program when some relation between machine states and
residual programs is preserved by one step: a related pair either returns the same value or
exposes the same query with related continuations. This reads `IsSimulation` at the level
of `view` and `FreeM` constructors, so clients never meet the implementation polynomial. -/

open PFunctor PFunctor.DynSystem PFunctor.DynSystem.DynComputation

namespace Model.Machine

universe u uA uB uα uβ

variable {p : PFunctor.{uA, uB}} {α : Type uα} {β : Type uβ} (M : DynComputation.{u} p α β)

/-- `R` is preserved by one synchronized step. -/
abbrev Steps (R : M.State → FreeM p β → Prop) : Prop :=
  ∀ s Q, R s Q →
    (∃ v, M.view s = .inl v ∧ Q = pure v) ∨
    (∃ (a : p.A) (next : p.B a → M.State) (k : p.B a → FreeM p β),
      M.view s = .inr ⟨a, next⟩ ∧ Q = FreeM.liftBind a k ∧ ∀ d, R (next d) (k d))

theorem behavior_eq_of_steps {R : M.State → FreeM p β → Prop} (h : Steps M R)
    {s : M.State} {Q : FreeM p β} (hR : R s Q) :
    M.toDynSystem.behavior s = FreeM.toResumption Q := by
  refine Resumption.bisim
    (fun l r => ∃ s Q, R s Q ∧ l = M.toDynSystem.behavior s ∧ r = FreeM.toResumption Q)
    ?_ ⟨s, Q, hR, rfl, rfl⟩
  rintro l r ⟨s, Q, hR, rfl, rfl⟩
  rcases h s Q hR with ⟨v, hv, rfl⟩ | ⟨a, next, k, hv, rfl, hnext⟩
  · exact .pure v (by rw [dest_behavior_view, hv]; rfl) (FreeM.dest_toResumption_pure v)
  · exact .query a (fun d => M.toDynSystem.behavior (next d)) (fun d => FreeM.toResumption (k d))
      (by rw [dest_behavior_view, hv]; rfl) (FreeM.dest_toResumption_liftBind a k)
      (fun d => ⟨next d, k d, hnext d, rfl, rfl⟩)

theorem implements_of_steps {R : M.State → FreeM p β → Prop} (h : Steps M R)
    (program : α → FreeM p β) (init : ∀ x, R (M.init x) (program x)) : M.Implements program :=
  fun x => behavior_eq_of_steps M h (init x)

/-- A state whose behavior is a program's and which returns `v` sits at `pure v`. -/
theorem eq_pure_of_view_inl {s : M.State} {P : FreeM p β}
    (hb : M.toDynSystem.behavior s = FreeM.toResumption P) {v : β} (hv : M.view s = .inl v) :
    P = pure v := by
  have h := congrArg Resumption.dest hb
  rw [dest_behavior_view, hv] at h
  cases P with
  | pure w =>
    have h' : Sum.inl v = Sum.inl w := h.trans (FreeM.dest_toResumption_pure w)
    exact congrArg (pure : β → FreeM p β) (Sum.inl.inj h').symm
  | liftBind a k =>
    rw [FreeM.dest_toResumption_liftBind] at h
    exact absurd h (by simp)

/-- A state whose behavior is a program's and which queries `a` sits at a `liftBind a`
whose continuations again have the continuation states' behaviors. -/
theorem exists_liftBind_of_view_inr {s : M.State} {P : FreeM p β}
    (hb : M.toDynSystem.behavior s = FreeM.toResumption P) {a : p.A} {next : p.B a → M.State}
    (hv : M.view s = .inr ⟨a, next⟩) :
    ∃ k : p.B a → FreeM p β, P = FreeM.liftBind a k ∧
      ∀ d, M.toDynSystem.behavior (next d) = FreeM.toResumption (k d) := by
  have h := congrArg Resumption.dest hb
  rw [dest_behavior_view, hv] at h
  cases P with
  | pure w => exact absurd h (by simp)
  | liftBind a' k =>
    rw [FreeM.dest_toResumption_liftBind] at h
    simp only [Sum.map_inr, Sum.inr.injEq] at h
    obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.mp h
    exact ⟨k, rfl, fun d => congrFun (eq_of_heq hk) d⟩

/-- A state whose behavior is a query program exposes that query, with continuation states
whose behaviors are the program's continuations. -/
theorem view_of_behavior_liftBind {s : M.State} {a : p.A} {k : p.B a → FreeM p β}
    (hb : M.toDynSystem.behavior s = FreeM.toResumption (FreeM.liftBind a k)) :
    ∃ next : p.B a → M.State, M.view s = .inr ⟨a, next⟩ ∧
      ∀ d, M.toDynSystem.behavior (next d) = FreeM.toResumption (k d) := by
  rcases hv : M.view s with v | ⟨a', next⟩
  · exact absurd (Machine.eq_pure_of_view_inl M hb hv) (by simp)
  · obtain ⟨k', hk, hnext⟩ := Machine.exists_liftBind_of_view_inr M hb hv
    cases hk
    exact ⟨next, rfl, hnext⟩

end Model.Machine
