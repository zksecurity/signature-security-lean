import Signatures.Runtime.Language
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.Support

/-! First-order oracle programs. Query handlers supply their complete execution, not just an
oracle price. Local syntax, argument evaluation, stack frames, and bounded loop control are
charged independently. A closed runtime certificate will restrict handlers to implemented
cryptographic primitives or recursively certified programs. -/

open OracleComp OracleSpec

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}
  {I : Type} {spec : OracleSpec I}

inductive Program {Atom : Type} (Op Cmd : Ty Atom → Ty Atom → Type) :
    List (Ty Atom) → Ty Atom → Type
  | ret {Γ a} : Expr Op Γ a → Program Op Cmd Γ a
  | query {Γ a b} : Cmd a b → Expr Op Γ a → Program Op Cmd Γ b
  | bind {Γ a b} : Program Op Cmd Γ a → Program Op Cmd (a :: Γ) b → Program Op Cmd Γ b
  | branch {Γ a} : Expr Op Γ .bool → Program Op Cmd Γ a → Program Op Cmd Γ a → Program Op Cmd Γ a
  | loop {Γ a} : Expr Op Γ .nat → Expr Op Γ a → Program Op Cmd (a :: Γ) a → Program Op Cmd Γ a
  | call {Γ Δ a} : Program Op Cmd Δ a → Args Op Γ Δ → Program Op Cmd Γ a

abbrev HandlerM (base : Atom → Type) (Cmd : Ty Atom → Ty Atom → Type) (m : Type → Type) :=
  {a b : Ty Atom} → Cmd a b → a.Value base → m (Run (b.Value base))

abbrev SemanticsM (base : Atom → Type) (Cmd : Ty Atom → Ty Atom → Type) (m : Type → Type) :=
  {a b : Ty Atom} → Cmd a b → a.Value base → m (b.Value base)

abbrev Handler (base : Atom → Type) (Cmd : Ty Atom → Ty Atom → Type) (spec : OracleSpec I) :=
  HandlerM base Cmd (OracleComp spec)

abbrev Semantics (base : Atom → Type) (Cmd : Ty Atom → Ty Atom → Type) (spec : OracleSpec I) :=
  SemanticsM base Cmd (OracleComp spec)

def repeatRun {m : Type → Type} [Monad m] {α : Type} (step : α → m (Run α)) : Nat → α → m (Run α)
  | 0, x => pure ⟨x, 1⟩
  | n + 1, x => do
      let r ← step x
      let z ← repeatRun step n r.value
      pure ⟨z.value, r.steps + z.steps + 2⟩

def repeatDenote {m : Type → Type} [Monad m] {α : Type} (step : α → m α) : Nat → α → m α
  | 0, x => pure x
  | n + 1, x => step x >>= repeatDenote step n

theorem repeatDenote_succ_right {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (step : α → m α) (n : Nat) (x : α) :
    repeatDenote step (n + 1) x = repeatDenote step n x >>= step := by
  induction n generalizing x with
  | zero => simp [repeatDenote]
  | succ n ih =>
      change (step x >>= repeatDenote step (n + 1)) = (step x >>= repeatDenote step n) >>= step
      simp only [bind_assoc]
      congr 1
      funext y
      exact ih y

theorem repeatRun_erase {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (step : α → m (Run α)) (n : Nat) (x : α) :
    Run.value <$> repeatRun step n x = repeatDenote (fun a => Run.value <$> step a) n x := by
  induction n generalizing x with
  | zero => simp [repeatRun, repeatDenote]
  | succ n ih => simp [repeatRun, repeatDenote, map_bind, bind_map_left, ← ih]

theorem repeatRun_steps_le {α : Type} (step : α → OracleComp spec (Run α)) (c : Nat)
    (h : ∀ x z, z ∈ support (step x) → z.steps ≤ c) (n : Nat) (x : α)
    (z : Run α) (hz : z ∈ support (repeatRun step n x)) : z.steps ≤ n * (c + 2) + 1 := by
  induction n generalizing x z with
  | zero =>
      simp only [repeatRun, support_pure, Set.mem_singleton_iff] at hz
      subst z
      simp
  | succ n ih =>
      simp only [repeatRun, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨r, hr, z, hz, rfl⟩ := hz
      have hi := ih r.value z hz
      have hs := h x r hr
      dsimp
      nlinarith

def Program.run {m : Type → Type} [Monad m] (P : Primitives base Op) (H : HandlerM base Cmd m) {Γ a} :
    Program Op Cmd Γ a → Env base Γ → m (Run (a.Value base))
  | .ret e, env =>
      let r := e.run P env
      pure ⟨r.value, r.steps + 1⟩
  | .query instr arg, env => do
      let x := arg.run P env
      let r ← H instr x.value
      pure ⟨r.value, x.steps + r.steps + 1⟩
  | .bind code body, env => do
      let x ← code.run P H env
      let r ← body.run P H (x.value, env)
      pure ⟨r.value, x.steps + r.steps + 1⟩
  | .branch cond yes no, env => do
      let b := cond.run P env
      let r ← if b.value = true then yes.run P H env else no.run P H env
      pure ⟨r.value, b.steps + r.steps + 1⟩
  | .loop count init body, env => do
      let n := count.run P env
      let x := init.run P env
      let r ← repeatRun (fun acc => body.run P H (acc, env)) n.value x.value
      pure ⟨r.value, n.steps + x.steps + r.steps + 1⟩
  | .call body args, env => do
      let input := args.run P env
      let r ← body.run P H input.value
      pure ⟨r.value, input.steps + r.steps + 2⟩

def Program.denote {m : Type → Type} [Monad m] (P : Primitives base Op) (H : SemanticsM base Cmd m) {Γ a} :
    Program Op Cmd Γ a → Env base Γ → m (a.Value base)
  | .ret e, env => pure (e.denote P env)
  | .query instr arg, env => H instr (arg.denote P env)
  | .bind code body, env => code.denote P H env >>= fun x => body.denote P H (x, env)
  | .branch cond yes no, env =>
      if cond.denote P env = true then yes.denote P H env else no.denote P H env
  | .loop count init body, env =>
      repeatDenote (fun acc => body.denote P H (acc, env)) (count.denote P env) (init.denote P env)
  | .call body args, env => body.denote P H (args.denote P env)

@[simp] theorem Program.run_erase {m : Type → Type} [Monad m] [LawfulMonad m]
    (P : Primitives base Op) (H : HandlerM base Cmd m)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    Run.value <$> code.run P H env = code.denote P (fun instr x => Run.value <$> H instr x) env := by
  induction code with
  | ret e => simp [run, denote]
  | query instr arg => simp [run, denote, map_eq_bind_pure_comp]
  | bind code body ih ihbody =>
      simp only [run, denote, map_bind, map_pure]
      simp only [bind_pure_comp]
      simp_rw [ihbody]
      rw [← ih, bind_map_left]
  | branch cond yes no ihyes ihno =>
      by_cases h : cond.denote P env = true <;>
        simp [run, denote, ← ihyes, ← ihno, h]
  | loop count init body ih =>
      simp only [run, denote, map_bind, map_pure]
      simp only [bind_pure_comp]
      simp_rw [repeatRun_erase, ih, Expr.run_value]
  | call body args ih => simp [run, denote, bind_pure_comp, ih]

/-- A query-free return still pays for evaluating its expression and returning the result. -/
theorem Program.ret_steps_pos (P : Primitives base Op) (H : Handler base Cmd spec)
    {Γ a} (e : Expr Op Γ a) (env : Env base Γ) (z : Run (a.Value base))
    (hz : z ∈ support ((Program.ret e).run P H env)) : 1 < z.steps := by
  simp only [run, support_pure, Set.mem_singleton_iff] at hz
  subst z
  have := e.steps_pos P env
  dsimp
  omega

end Signatures.Runtime
