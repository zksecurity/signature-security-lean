import Mathlib.Tactic.Linarith

/-!
# First-order local runtime

This is an explicit stack-and-list machine, not a cost annotation on a Lean function.
Programs cannot embed host-language functions. The only semantic parameters are a typed
instruction set and its primitive implementation/cost contract. Cryptographic arithmetic
will be instantiated by named instructions, not arbitrary functions supplied as instructions.

Stack access pays one unit per cell. Constructors, projections, branches, and loop control
pay one unit each; pushing a local binding also pays one. Integer literals use a conservative
unary loading cost. These are arithmetic-machine steps, not Lean VM or bit-level time.
-/

namespace Signatures.Runtime

inductive Ty (Atom : Type) where
  | atom : Atom → Ty Atom
  | unit : Ty Atom
  | bool : Ty Atom
  | nat : Ty Atom
  | pair : Ty Atom → Ty Atom → Ty Atom
  | list : Ty Atom → Ty Atom

@[reducible] def Ty.Value {Atom : Type} (base : Atom → Type) : Ty Atom → Type
  | .atom a => base a
  | .unit => Unit
  | .bool => Bool
  | .nat => Nat
  | .pair a b => a.Value base × b.Value base
  | .list a => List (a.Value base)

inductive Var {Atom : Type} : List (Ty Atom) → Ty Atom → Type
  | here {a Γ} : Var (a :: Γ) a
  | there {a b Γ} : Var Γ a → Var (b :: Γ) a

def Var.depth {Atom : Type} {Γ : List (Ty Atom)} {a : Ty Atom} : Var Γ a → Nat
  | .here => 0
  | .there v => v.depth + 1

@[reducible] def Env {Atom : Type} (base : Atom → Type) : List (Ty Atom) → Type
  | [] => Unit
  | a :: Γ => a.Value base × Env base Γ

def Var.get {Atom : Type} {base : Atom → Type} {Γ : List (Ty Atom)} {a : Ty Atom} :
    Var Γ a → Env base Γ → a.Value base
  | .here, env => env.1
  | .there v, env => v.get env.2

structure Run (α : Type) where
  value : α
  steps : Nat
  deriving Repr

/-- Primitive instructions must come from a fixed instruction family. The contract is the
explicit boundary for field/group operations and their concrete implementation costs. -/
structure Primitives {Atom : Type} (base : Atom → Type) (Op : Ty Atom → Ty Atom → Type) where
  execute : {a b : Ty Atom} → Op a b → a.Value base → b.Value base
  cost : {a b : Ty Atom} → Op a b → a.Value base → Nat

inductive Expr {Atom : Type} (Op : Ty Atom → Ty Atom → Type) :
    List (Ty Atom) → Ty Atom → Type
  | var {Γ a} : Var Γ a → Expr Op Γ a
  | unit {Γ} : Expr Op Γ .unit
  | bool {Γ} : Bool → Expr Op Γ .bool
  | nat {Γ} : Nat → Expr Op Γ .nat
  | pair {Γ a b} : Expr Op Γ a → Expr Op Γ b → Expr Op Γ (.pair a b)
  | fst {Γ a b} : Expr Op Γ (.pair a b) → Expr Op Γ a
  | snd {Γ a b} : Expr Op Γ (.pair a b) → Expr Op Γ b
  | nil {Γ a} : Expr Op Γ (.list a)
  | cons {Γ a} : Expr Op Γ a → Expr Op Γ (.list a) → Expr Op Γ (.list a)
  | branch {Γ a} : Expr Op Γ .bool → Expr Op Γ a → Expr Op Γ a → Expr Op Γ a
  | letE {Γ a b} : Expr Op Γ a → Expr Op (a :: Γ) b → Expr Op Γ b
  | op {Γ a b} : Op a b → Expr Op Γ a → Expr Op Γ b
  | fold {Γ a b} : Expr Op Γ (.list a) → Expr Op Γ b →
      Expr Op (a :: b :: Γ) b → Expr Op Γ b

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}

/-- A left fold with explicit environment frames and termination tests. -/
def foldRun {α β : Type} (step : α → β → Run β) : List α → β → Run β
  | [], acc => ⟨acc, 1⟩
  | x :: xs, acc =>
      let r := step x acc
      let tail := foldRun step xs r.value
      ⟨tail.value, r.steps + tail.steps + 3⟩

def Expr.run (P : Primitives base Op) {Γ a} : Expr Op Γ a → Env base Γ → Run (a.Value base)
  | .var v, env => ⟨v.get env, v.depth + 1⟩
  | .unit, _ => ⟨(), 1⟩
  | .bool b, _ => ⟨b, 1⟩
  | .nat n, _ => ⟨n, n + 1⟩
  | .pair l r, env =>
      let x := l.run P env
      let y := r.run P env
      ⟨(x.value, y.value), x.steps + y.steps + 1⟩
  | .fst p, env => let r := p.run P env; ⟨r.value.1, r.steps + 1⟩
  | .snd p, env => let r := p.run P env; ⟨r.value.2, r.steps + 1⟩
  | .nil, _ => ⟨[], 1⟩
  | .cons h t, env =>
      let x := h.run P env
      let xs := t.run P env
      ⟨x.value :: xs.value, x.steps + xs.steps + 1⟩
  | .branch c t f, env =>
      let b := c.run P env
      let r := if b.value = true then t.run P env else f.run P env
      ⟨r.value, b.steps + r.steps + 1⟩
  | .letE e body, env =>
      let x := e.run P env
      let r := body.run P (x.value, env)
      ⟨r.value, x.steps + r.steps + 1⟩
  | .op instr e, env =>
      let x := e.run P env
      ⟨P.execute instr x.value, x.steps + P.cost instr x.value + 1⟩
  | .fold xs init body, env =>
      let input := xs.run P env
      let start := init.run P env
      let r := foldRun (fun x acc => body.run P (x, acc, env)) input.value start.value
      ⟨r.value, input.steps + start.steps + r.steps + 1⟩

def Expr.denote (P : Primitives base Op) {Γ a} : Expr Op Γ a → Env base Γ → a.Value base
  | .var v, env => v.get env
  | .unit, _ => ()
  | .bool b, _ => b
  | .nat n, _ => n
  | .pair l r, env => (l.denote P env, r.denote P env)
  | .fst p, env => (p.denote P env).1
  | .snd p, env => (p.denote P env).2
  | .nil, _ => []
  | .cons h t, env => h.denote P env :: t.denote P env
  | .branch c t f, env => if c.denote P env = true then t.denote P env else f.denote P env
  | .letE e body, env => body.denote P (e.denote P env, env)
  | .op instr e, env => P.execute instr (e.denote P env)
  | .fold xs init body, env =>
      (xs.denote P env).foldl (fun acc x => body.denote P (x, acc, env)) (init.denote P env)

theorem foldRun_value {α β : Type} (step : α → β → Run β) (xs : List α) (acc : β) :
    (foldRun step xs acc).value = xs.foldl (fun acc x => (step x acc).value) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih => simpa [foldRun] using ih (step x acc).value

@[simp] theorem Expr.run_value (P : Primitives base Op) {Γ a} (e : Expr Op Γ a)
    (env : Env base Γ) : (e.run P env).value = e.denote P env := by
  induction e with
  | var v => rfl
  | unit => rfl
  | bool b => rfl
  | nat n => rfl
  | pair l r ihl ihr => simp [run, denote, ihl, ihr]
  | fst p ih => simp [run, denote, ih]
  | snd p ih => simp [run, denote, ih]
  | nil => rfl
  | cons h t ihh iht => simp [run, denote, ihh, iht]
  | branch c t f ihc iht ihf =>
      by_cases h : c.denote P env = true <;> simp [run, denote, ihc, iht, ihf, h]
  | letE e body ihe ihbody => simp [run, denote, ihe, ihbody]
  | op op e ih => simp [run, denote, ih]
  | fold xs init body ihxs ihinit ihbody =>
      simp [run, denote, ihxs, ihinit, foldRun_value, ihbody]

/-- No expression, including a pure one, is assigned zero local runtime. -/
theorem Expr.steps_pos (P : Primitives base Op) {Γ a} (e : Expr Op Γ a)
    (env : Env base Γ) : 0 < (e.run P env).steps := by
  cases e <;> simp [run]

theorem foldRun_steps_le {α β : Type} (step : α → β → Run β)
    (bound : Nat) (h : ∀ x acc, (step x acc).steps ≤ bound) (xs : List α) (acc : β) :
    (foldRun step xs acc).steps ≤ xs.length * (bound + 3) + 1 := by
  induction xs generalizing acc with
  | nil => simp [foldRun]
  | cons x xs ih =>
      have hi := ih (step x acc).value
      have hx := h x acc
      simp only [foldRun, List.length_cons]
      nlinarith

/-- A procedure's argument frame is built from expressions, never from an arbitrary
host-language environment function. Each evaluated argument and frame cell is charged. -/
inductive Args (Op : Ty Atom → Ty Atom → Type) (Γ : List (Ty Atom)) : List (Ty Atom) → Type
  | nil : Args Op Γ []
  | cons {a Δ} : Expr Op Γ a → Args Op Γ Δ → Args Op Γ (a :: Δ)

def Args.run (P : Primitives base Op) {Γ Δ} : Args Op Γ Δ → Env base Γ → Run (Env base Δ)
  | .nil, _ => ⟨(), 1⟩
  | .cons head tail, env =>
      let x := head.run P env
      let xs := tail.run P env
      ⟨(x.value, xs.value), x.steps + xs.steps + 1⟩

def Args.denote (P : Primitives base Op) {Γ Δ} : Args Op Γ Δ → Env base Γ → Env base Δ
  | .nil, _ => ()
  | .cons head tail, env => (head.denote P env, tail.denote P env)

@[simp] theorem Args.run_value (P : Primitives base Op) {Γ Δ} (args : Args Op Γ Δ) (env : Env base Γ) :
    (args.run P env).value = args.denote P env := by
  induction args with
  | nil => rfl
  | cons head tail ih => simp [run, denote, ih]

theorem Args.steps_pos (P : Primitives base Op) {Γ Δ} (args : Args Op Γ Δ) (env : Env base Γ) :
    0 < (args.run P env).steps := by
  cases args <;> simp [run]

end Signatures.Runtime
