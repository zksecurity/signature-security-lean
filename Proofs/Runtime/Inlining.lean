import Proofs.Runtime.Program

/-! Compile oracle capabilities to ordinary first-order procedures. A routine is syntax,
not an opaque semantic function. Exact runtime equality accounts for argument evaluation,
frame construction, entering the procedure, and returning to the caller. -/

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type}
  {Op Cmd Target : Ty Atom → Ty Atom → Type}

def Program.inline (routines : {a b : Ty Atom} → Cmd a b → Program Op Target [a] b)
    {Γ a} : Program Op Cmd Γ a → Program Op Target Γ a
  | .ret e => .ret e
  | .query cmd arg => .call (routines cmd) (.cons arg .nil)
  | .bind code body => .bind (code.inline routines) (body.inline routines)
  | .branch cond yes no => .branch cond (yes.inline routines) (no.inline routines)
  | .loop count init body => .loop count init (body.inline routines)
  | .call body args => .call (body.inline routines) args

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Relative to the source query node, a one-argument call adds three frame steps.
The full callee execution remains present; it is never replaced by an assumed cost. -/
def routineHandler (P : Primitives base Op) (H : HandlerM base Target m)
    (routines : {a b : Ty Atom} → Cmd a b → Program Op Target [a] b) : HandlerM base Cmd m :=
  fun cmd arg => do
    let r ← (routines cmd).run P H (arg, ())
    pure ⟨r.value, r.steps + 3⟩

theorem Program.inline_run (P : Primitives base Op) (H : HandlerM base Target m)
    (routines : {a b : Ty Atom} → Cmd a b → Program Op Target [a] b)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    (code.inline routines).run P H env = code.run P (routineHandler P H routines) env := by
  induction code with
  | ret e => rfl
  | query cmd arg =>
      simp [inline, run, Args.run, routineHandler, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      congr 1
      funext r
      congr 1
      omega
  | bind code body ih ihbody => simp [inline, run, ih, ihbody]
  | branch cond yes no ihyes ihno => simp [inline, run, ihyes, ihno]
  | loop count init body ih => simp [inline, run, ih]
  | call body args ih => simp [inline, run, ih]

omit [LawfulMonad m] in
theorem Program.inline_denote (P : Primitives base Op) (H : SemanticsM base Target m)
    (routines : {a b : Ty Atom} → Cmd a b → Program Op Target [a] b)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) :
    (code.inline routines).denote P H env =
      code.denote P (fun cmd arg => (routines cmd).denote P H (arg, ())) env := by
  induction code with
  | ret e => rfl
  | query cmd arg => rfl
  | bind code body ih ihbody => simp [inline, denote, ih, ihbody]
  | branch cond yes no ihyes ihno => simp [inline, denote, ihyes, ihno]
  | loop count init body ih => simp [inline, denote, ih]
  | call body args ih => simp [inline, denote, ih]

end Signatures.Runtime
