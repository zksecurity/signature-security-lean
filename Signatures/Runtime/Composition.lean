import Signatures.Runtime.Program

/-!
# Runtime composition with stateful oracle handlers

The comparison below is pathwise and support-based. It transports runtime bounds, not
probabilities. All local expression, stack, branch, and loop costs remain those of `Program.run`.
Only individual handler calls need comparison certificates. State invariants are propagated
through arbitrary response-dependent continuations.
-/

open OracleComp OracleSpec

namespace Signatures.Runtime

variable {I J S α : Type} {target : OracleSpec I} {source : OracleSpec J}

def DominatedBy (inv : S → Prop) (potential : S → Int)
    (implementation : StateT S (OracleComp target) (Run α))
    (reference : OracleComp source (Run α)) : Prop :=
  ∀ s, inv s → ∀ z ∈ support (implementation.run s),
    inv z.2 ∧ ∃ r ∈ support reference, r.value = z.1.value ∧
      (z.1.steps : Int) + potential z.2 ≤ (r.steps : Int) + potential s

theorem repeatRun_dominated (inv : S → Prop) (potential : S → Int)
    (implementation : α → StateT S (OracleComp target) (Run α))
    (reference : α → OracleComp source (Run α))
    (hstep : ∀ x, DominatedBy inv potential (implementation x) (reference x)) (n : Nat) (x : α) :
    DominatedBy inv potential (repeatRun implementation n x) (repeatRun reference n x) := by
  intro s hs z hz
  induction n generalizing x s z with
  | zero =>
      simp only [repeatRun, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hs, ⟨x, 1⟩, by simp [repeatRun], rfl, le_rfl⟩
  | succ n ih =>
      simp only [repeatRun, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s₁⟩, hr, ⟨u, s₂⟩, hu, rfl⟩ := hz
      obtain ⟨hs₁, r', hr', hv, hc⟩ := hstep x s hs (r, s₁) hr
      obtain ⟨hs₂, u', hu', huv, huc⟩ := ih r.value s₁ hs₁ (u, s₂) hu
      refine ⟨hs₂, ⟨u'.value, r'.steps + u'.steps + 2⟩, ?_, huv, ?_⟩
      · simp only [repeatRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨r', hr', u', by simpa [hv] using hu', rfl⟩
      · dsimp at hc huc ⊢
        omega

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}

/-- Per-handler implementation certificates compose through the complete source syntax.
Neither the complete simulator bound nor a bound on the finished reduction is a premise. -/
theorem Program.run_dominated (P : Primitives base Op) (inv : S → Prop) (potential : S → Int)
    (implementation : HandlerM base Cmd (StateT S (OracleComp target)))
    (reference : Handler base Cmd source)
    (hhandler : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base),
      DominatedBy inv potential (implementation cmd arg) (reference cmd arg))
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    DominatedBy inv potential (code.run P implementation env) (code.run P reference env) := by
  induction code with
  | ret e =>
      intro s hs z hz
      simp only [run, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      subst z
      exact ⟨hs, ⟨(e.run P env).value, (e.run P env).steps + 1⟩, by simp [run], rfl, le_rfl⟩
  | query cmd arg =>
      intro s hs z hz
      simp only [run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
      obtain ⟨hs', r', hr', hv, hc⟩ := hhandler cmd (arg.run P env).value s hs (r, s') hr
      refine ⟨hs', ⟨r'.value, (arg.run P env).steps + r'.steps + 1⟩, ?_, hv, ?_⟩
      · simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨r', hr', rfl⟩
      · dsimp at hc ⊢
        omega
  | bind code body ih ihbody =>
      intro s hs z hz
      simp only [run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s₁⟩, hr, ⟨u, s₂⟩, hu, rfl⟩ := hz
      obtain ⟨hs₁, r', hr', hv, hc⟩ := ih env s hs (r, s₁) hr
      obtain ⟨hs₂, u', hu', huv, huc⟩ := ihbody (r.value, env) s₁ hs₁ (u, s₂) hu
      refine ⟨hs₂, ⟨u'.value, r'.steps + u'.steps + 1⟩, ?_, huv, ?_⟩
      · simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨r', hr', u', by simpa [hv] using hu', rfl⟩
      · dsimp at hc huc ⊢
        omega
  | branch cond yes no ihyes ihno =>
      intro s hs z hz
      by_cases hb : (cond.run P env).value = true
      · simp only [run, hb, ite_true, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
        obtain ⟨hs', r', hr', hv, hc⟩ := ihyes env s hs (r, s') hr
        refine ⟨hs', ⟨r'.value, (cond.run P env).steps + r'.steps + 1⟩, ?_, hv, ?_⟩
        · simp only [run, hb, ite_true, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
          exact ⟨r', hr', rfl⟩
        · dsimp at hc ⊢
          omega
      · simp only [run, hb, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
        obtain ⟨hs', r', hr', hv, hc⟩ := ihno env s hs (r, s') hr
        refine ⟨hs', ⟨r'.value, (cond.run P env).steps + r'.steps + 1⟩, ?_, hv, ?_⟩
        · simp only [run, hb, Bool.false_eq_true, ite_false, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
          exact ⟨r', hr', rfl⟩
        · dsimp at hc ⊢
          omega
  | loop count init body ih =>
      intro s hs z hz
      simp only [run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
      obtain ⟨hs', r', hr', hv, hc⟩ := repeatRun_dominated inv potential
        (fun acc => body.run P implementation (acc, env))
        (fun acc => body.run P reference (acc, env))
        (fun acc => ih (acc, env)) (count.run P env).value (init.run P env).value s hs (r, s') hr
      refine ⟨hs', ⟨r'.value, (count.run P env).steps + (init.run P env).steps + r'.steps + 1⟩,
        ?_, hv, ?_⟩
      · simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨r', hr', rfl⟩
      · dsimp at hc ⊢
        omega

  | call body args ih =>
      intro s hs z hz
      simp only [run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
      obtain ⟨hs', r', hr', hv, hc⟩ := ih (args.run P env).value s hs (r, s') hr
      refine ⟨hs', ⟨r'.value, (args.run P env).steps + r'.steps + 2⟩, ?_, hv, ?_⟩
      · simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨r', hr', rfl⟩
      · dsimp at hc ⊢
        omega

end Signatures.Runtime
