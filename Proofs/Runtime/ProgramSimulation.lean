import Proofs.Runtime.Program

/-! Interpreting effects preserves the complete source execution, including
its counters. This applies to probability interpreters as well as oracle trees. -/

namespace Signatures.Runtime

variable {m n : Type → Type} [Monad m] [Monad n]

theorem repeatRun_mmap (f : m →ᵐ n) {A : Type} (step : A → m (Run A)) (k : Nat) (x : A) :
    f (repeatRun step k x) = repeatRun (fun a => f (step a)) k x := by
  induction k generalizing x with
  | zero => simp [repeatRun]
  | succ k ih => simp [repeatRun, ih]

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}

theorem repeatDenote_mmap (f : m →ᵐ n) {A : Type} (step : A → m A) (k : Nat) (x : A) :
    f (repeatDenote step k x) = repeatDenote (fun a => f (step a)) k x := by
  induction k generalizing x with
  | zero => simp [repeatDenote]
  | succ k ih => simp [repeatDenote, ih]

theorem Program.denote_mmap (f : m →ᵐ n) (P : Primitives base Op) (H : SemanticsM base Cmd m)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    f (code.denote P H env) = code.denote P (fun cmd arg => f (H cmd arg)) env := by
  induction code with
  | ret e => simp [denote]
  | query cmd arg => rfl
  | bind first body ih ihbody => simp [denote, ih, ihbody]
  | branch cond yes no ihyes ihno =>
    simp only [denote]
    split <;> simp_all
  | loop count init body ih => simp [denote, repeatDenote_mmap, ih]
  | call body args ih => exact ih (args.denote P env)

theorem Program.run_mmap (f : m →ᵐ n) (P : Primitives base Op) (H : HandlerM base Cmd m)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    f (code.run P H env) = code.run P (fun cmd arg => f (H cmd arg)) env := by
  induction code with
  | ret e => simp [run]
  | query cmd arg => simp [run]
  | bind first body ih ihbody => simp [run, ih, ihbody]
  | branch cond yes no ihyes ihno =>
    simp only [run]
    split <;> simp_all
  | loop count init body ih => simp [run, repeatRun_mmap, ih]
  | call body args ih => simp [run, ih]

namespace Simulation

/-- Reassociate state without changing either the execution or its law. -/
def flatten [LawfulMonad m] {S T : Type} : StateT S (StateT T m) →ᵐ StateT (S × T) m where
  toFun {_} code state := (fun out => (out.1.1, out.1.2, out.2)) <$> ((code.run state.1).run state.2)
  toFun_pure' x := by
    funext state
    change (fun out => (out.1.1, out.1.2, out.2)) <$> (pure ((x, state.1), state.2) : m _) = pure (x, state)
    simp
  toFun_bind' code next := by
    funext state
    change (fun out => (out.1.1, out.1.2, out.2)) <$>
      (code state.1 state.2 >>= fun out => next out.1.1 out.1.2 out.2) =
      ((fun out => (out.1.1, out.1.2, out.2)) <$> code state.1 state.2) >>=
        (fun out => (fun z => (z.1.1, z.1.2, z.2)) <$> next out.1 out.2.1 out.2.2)
    simp [map_bind, bind_map_left]

end Simulation

end Signatures.Runtime
