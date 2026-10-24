import Proofs.Runtime.Program

/-! Support inclusion across different oracle interfaces and state encodings.
This transports pathwise budgets, not probability or security bounds. -/

namespace Signatures.Runtime

open OracleComp

variable {I J S T A B : Type} {target : OracleSpec I} {source : OracleSpec J}

def StateSupportRefines (repr : S → T)
    (implementation : StateT S (OracleComp target) A)
    (reference : StateT T (OracleComp source) A) : Prop :=
  ∀ state out, out ∈ support (implementation.run state) →
    (out.1, repr out.2) ∈ support (reference.run (repr state))

theorem StateSupportRefines.pure (repr : S → T) (x : A) :
    StateSupportRefines repr (pure x : StateT S (OracleComp target) A)
      (pure x : StateT T (OracleComp source) A) := by
  intro state out hout
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout ⊢
  subst out
  rfl

theorem StateSupportRefines.bind (repr : S → T)
    {a : StateT S (OracleComp target) A} {b : StateT T (OracleComp source) A}
    {f : A → StateT S (OracleComp target) B} {g : A → StateT T (OracleComp source) B}
    (ha : StateSupportRefines repr a b) (hf : ∀ x, StateSupportRefines repr (f x) (g x)) :
    StateSupportRefines repr (a >>= f) (b >>= g) := by
  intro state out hout
  simp only [StateT.run_bind, mem_support_bind_iff] at hout ⊢
  obtain ⟨mid, hp, hout⟩ := hout
  exact ⟨(mid.1, repr mid.2), ha state mid hp, hf mid.1 mid.2 out hout⟩

theorem repeatRun_support_refines (repr : S → T)
    (step : A → StateT S (OracleComp target) (Run A))
    (reference : A → StateT T (OracleComp source) (Run A))
    (h : ∀ x, StateSupportRefines repr (step x) (reference x)) (n : Nat) (x : A) :
    StateSupportRefines repr (repeatRun step n x) (repeatRun reference n x) := by
  induction n generalizing x with
  | zero => exact .pure repr _
  | succ n ih =>
    apply StateSupportRefines.bind repr (h x)
    intro r
    apply StateSupportRefines.bind repr (ih r.value)
    intro z
    exact .pure repr _

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}

/-- Equal source results and step counts are preserved through adaptive syntax;
only support inclusion of the primitive handlers is needed. -/
theorem Program.run_support_refines (P : Primitives base Op) (repr : S → T)
    (implementation : HandlerM base Cmd (StateT S (OracleComp target)))
    (reference : HandlerM base Cmd (StateT T (OracleComp source)))
    (h : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base),
      StateSupportRefines repr (implementation cmd arg) (reference cmd arg))
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    StateSupportRefines repr (code.run P implementation env) (code.run P reference env) := by
  induction code with
  | ret e => exact .pure repr _
  | query cmd arg =>
    exact StateSupportRefines.bind repr (h cmd _) (fun _ => .pure repr _)
  | bind first body ih ihbody =>
    apply StateSupportRefines.bind repr (ih env)
    intro r
    exact StateSupportRefines.bind repr (ihbody (r.value, env)) (fun _ => .pure repr _)
  | branch cond yes no ihyes ihno =>
    by_cases hc : (cond.run P env).value = true
    · simp only [run, hc, ite_true]
      exact StateSupportRefines.bind repr (ihyes env) (fun _ => .pure repr _)
    · simp only [run, hc, Bool.false_eq_true, ite_false]
      exact StateSupportRefines.bind repr (ihno env) (fun _ => .pure repr _)
  | loop count init body ih =>
    apply StateSupportRefines.bind repr (repeatRun_support_refines repr _ _ (fun x => ih (x, env)) _ _)
    intro r
    exact .pure repr _
  | call body args ih =>
    exact StateSupportRefines.bind repr (ih (args.run P env).value) (fun _ => .pure repr _)

end Signatures.Runtime
