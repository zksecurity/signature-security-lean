import Proofs.Runtime.Program

/-! State-representation refinement, preserving both results and charged runtime through
adaptive control flow. The representation map is used in proofs only. -/

namespace Signatures.Runtime

variable {m : Type → Type} [Monad m] [LawfulMonad m] {S T α β : Type}

def StateRefines (repr : S → T) (implementation : StateT S m α) (reference : StateT T m α) : Prop :=
  ∀ s, (fun p => (p.1, repr p.2)) <$> implementation.run s = reference.run (repr s)

theorem StateRefines.pure (repr : S → T) (x : α) :
    StateRefines repr (pure x : StateT S m α) (pure x : StateT T m α) := by
  intro s
  simp

theorem StateRefines.bind (repr : S → T) {a : StateT S m α} {b : StateT T m α}
    {f : α → StateT S m β} {g : α → StateT T m β}
    (ha : StateRefines repr a b) (hf : ∀ x, StateRefines repr (f x) (g x)) :
    StateRefines repr (a >>= f) (b >>= g) := by
  intro s
  simp only [StateT.run_bind, map_bind]
  rw [← ha s, bind_map_left]
  congr 1
  funext p
  exact hf p.1 p.2

theorem repeatRun_refines (repr : S → T) (step : α → StateT S m (Run α))
    (reference : α → StateT T m (Run α))
    (h : ∀ x, StateRefines repr (step x) (reference x)) (n : Nat) (x : α) :
    StateRefines repr (repeatRun step n x) (repeatRun reference n x) := by
  induction n generalizing x with
  | zero => exact StateRefines.pure repr _
  | succ n ih =>
      apply StateRefines.bind repr (h x)
      intro r
      apply StateRefines.bind repr (ih r.value)
      intro z
      exact StateRefines.pure repr _

theorem repeatDenote_refines (repr : S → T) (step : α → StateT S m α)
    (reference : α → StateT T m α)
    (h : ∀ x, StateRefines repr (step x) (reference x)) (n : Nat) (x : α) :
    StateRefines repr (repeatDenote step n x) (repeatDenote reference n x) := by
  induction n generalizing x with
  | zero => exact StateRefines.pure repr _
  | succ n ih => exact StateRefines.bind repr (h x) ih

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}

theorem Program.run_refines (P : Primitives base Op) (repr : S → T)
    (implementation : HandlerM base Cmd (StateT S m))
    (reference : HandlerM base Cmd (StateT T m))
    (h : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base),
      StateRefines repr (implementation cmd arg) (reference cmd arg))
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    StateRefines repr (code.run P implementation env) (code.run P reference env) := by
  induction code with
  | ret e => exact StateRefines.pure repr _
  | query cmd arg =>
      apply StateRefines.bind repr (h cmd _)
      intro r
      exact StateRefines.pure repr _
  | bind code body ih ihbody =>
      apply StateRefines.bind repr (ih env)
      intro r
      apply StateRefines.bind repr (ihbody (r.value, env))
      intro z
      exact StateRefines.pure repr _
  | branch cond yes no ihyes ihno =>
      by_cases hc : (cond.run P env).value = true
      · simp only [run, hc, ite_true]
        exact StateRefines.bind repr (ihyes env) (fun _ => StateRefines.pure repr _)
      · simp only [run, hc, Bool.false_eq_true, ite_false]
        exact StateRefines.bind repr (ihno env) (fun _ => StateRefines.pure repr _)
  | loop count init body ih =>
      apply StateRefines.bind repr (repeatRun_refines repr _ _ (fun x => ih (x, env)) _ _)
      intro r
      exact StateRefines.pure repr _
  | call body args ih =>
      exact StateRefines.bind repr (ih (args.run P env).value) (fun _ => StateRefines.pure repr _)

theorem Program.denote_refines (P : Primitives base Op) (repr : S → T)
    (implementation : SemanticsM base Cmd (StateT S m))
    (reference : SemanticsM base Cmd (StateT T m))
    (h : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base),
      StateRefines repr (implementation cmd arg) (reference cmd arg))
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    StateRefines repr (code.denote P implementation env) (code.denote P reference env) := by
  induction code with
  | ret e => exact StateRefines.pure repr _
  | query cmd arg => exact h cmd _
  | bind code body ih ihbody => exact StateRefines.bind repr (ih env) (fun x => ihbody (x, env))
  | branch cond yes no ihyes ihno =>
      simp only [denote]
      split <;> first | exact ihyes env | exact ihno env
  | loop count init body ih => exact repeatDenote_refines repr _ _ (fun x => ih (x, env)) _ _
  | call body args ih => exact ih (args.denote P env)

open OracleComp

theorem repeatDenote_simulate {I : Type} {spec : OracleSpec I}
    (implementation : QueryImpl spec m) (step : α → OracleComp spec α) (n : Nat) (x : α) :
    simulateQ implementation (repeatDenote step n x) =
      repeatDenote (fun x => simulateQ implementation (step x)) n x := by
  induction n generalizing x with
  | zero => simp [repeatDenote]
  | succ n ih => simp [repeatDenote, ih]

/-- Interpreting a source program and then simulating its requests is exactly the same
computation as running its semantic interpreter with the simulated handlers. -/
theorem Program.denote_simulate {I : Type} {spec : OracleSpec I}
    (P : Primitives base Op) (implementation : QueryImpl spec m)
    (H : Semantics base Cmd spec) {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    simulateQ implementation (code.denote P H env) =
      code.denote P (fun cmd arg => simulateQ implementation (H cmd arg)) env := by
  induction code with
  | ret e => simp [denote]
  | query cmd arg => rfl
  | bind code body ih ihbody => simp [denote, ih, ihbody]
  | branch cond yes no ihyes ihno =>
      by_cases hc : cond.denote P env = true <;> simp [denote, hc, ihyes, ihno]
  | loop count init body ih => simp [denote, repeatDenote_simulate, ih]
  | call body args ih => exact ih (args.denote P env)

/-- Ghost instrumentation only: records how many handler calls have occurred, without
altering their charged steps. It is erased by `Program.countCalls_refines`. No implementation
is allowed a free counter operation; this counter is absent from the executed program. -/
def countCalls (H : HandlerM base Cmd (StateT S m)) : HandlerM base Cmd (StateT (S × Nat) m) :=
  fun cmd arg state => do
    let p ← (H cmd arg).run state.1
    pure (p.1, (p.2, state.2 + 1))

theorem countCalls_refines (H : HandlerM base Cmd (StateT S m))
    {a b} (cmd : Cmd a b) (arg : a.Value base) :
    StateRefines Prod.fst (countCalls H cmd arg) (H cmd arg) := by
  intro state
  simp [countCalls, StateT.run, bind_pure_comp]

theorem Program.countCalls_refines (P : Primitives base Op)
    (H : HandlerM base Cmd (StateT S m)) {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    StateRefines Prod.fst (code.run P (countCalls H) env) (code.run P H env) :=
  code.run_refines P Prod.fst (countCalls H) H (Signatures.Runtime.countCalls_refines H) env

end Signatures.Runtime
