import Signatures.Runtime.Data

/-! Reuse first-order expressions in a larger trailing register context. This is a
syntax transformation; register depths and executed costs are preserved exactly. -/

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}

def Var.weakenTail {Γ : List (Ty Atom)} {a : Ty Atom} (Δ : List (Ty Atom)) :
    Var Γ a → Var (Γ ++ Δ) a
  | .here => .here
  | .there v => .there (v.weakenTail Δ)

@[simp] theorem Var.weakenTail_depth {Γ : List (Ty Atom)} {a : Ty Atom}
    (v : Var Γ a) (Δ : List (Ty Atom)) : (v.weakenTail Δ).depth = v.depth := by
  induction v <;> simp_all [weakenTail, depth]

@[simp] theorem Var.weakenTail_get {Γ Δ : List (Ty Atom)} {a : Ty Atom}
    (v : Var Γ a) (env : Env base Γ) (tail : Env base Δ) :
    (v.weakenTail Δ).get (Env.append env tail) = v.get env := by
  induction v with
  | here => rfl
  | there v ih => exact ih env.2

def Expr.weakenTail {Γ : List (Ty Atom)} {a : Ty Atom} (Δ : List (Ty Atom)) :
    Expr Op Γ a → Expr Op (Γ ++ Δ) a
  | .var v => .var (v.weakenTail Δ)
  | .unit => .unit
  | .bool b => .bool b
  | .nat n => .nat n
  | .pair l r => .pair (l.weakenTail Δ) (r.weakenTail Δ)
  | .fst p => .fst (p.weakenTail Δ)
  | .snd p => .snd (p.weakenTail Δ)
  | .nil => .nil
  | .cons h t => .cons (h.weakenTail Δ) (t.weakenTail Δ)
  | .branch c t f => .branch (c.weakenTail Δ) (t.weakenTail Δ) (f.weakenTail Δ)
  | .letE e body => .letE (e.weakenTail Δ) (body.weakenTail Δ)
  | .op instr e => .op instr (e.weakenTail Δ)
  | .fold xs init body => .fold (xs.weakenTail Δ) (init.weakenTail Δ) (body.weakenTail Δ)

theorem Expr.weakenTail_run (P : Primitives base Op) {Γ Δ : List (Ty Atom)} {a : Ty Atom}
    (e : Expr Op Γ a) (env : Env base Γ) (tail : Env base Δ) :
    (e.weakenTail Δ).run P (Env.append env tail) = e.run P env := by
  induction e with
  | var v => simp [weakenTail, run]
  | unit => rfl
  | bool b => rfl
  | nat n => rfl
  | pair l r ihl ihr => simp only [weakenTail, run, ihl, ihr]
  | fst p ih => simp only [weakenTail, run, ih]
  | snd p ih => simp only [weakenTail, run, ih]
  | nil => rfl
  | cons h t ihh iht => simp only [weakenTail, run, ihh, iht]
  | branch c t f ihc iht ihf => simp only [weakenTail, run, ihc, iht, ihf]
  | letE e body ihe ihbody =>
      simp only [weakenTail, run, ihe]
      have hb := ihbody ((e.run P env).value, env)
      dsimp [Env.append] at hb
      rw [hb]
  | op instr e ih => simp only [weakenTail, run, ih]
  | fold xs init body ihxs ihinit ihbody =>
      simp only [weakenTail, run, ihxs, ihinit]
      have hb : (fun x acc => (body.weakenTail Δ).run P (x, acc, env.append tail)) =
          fun x acc => body.run P (x, acc, env) := by
        funext x acc
        exact ihbody (x, acc, env)
      rw [hb]

theorem Expr.weakenTail_denote (P : Primitives base Op) {Γ Δ : List (Ty Atom)} {a : Ty Atom}
    (e : Expr Op Γ a) (env : Env base Γ) (tail : Env base Δ) :
    (e.weakenTail Δ).denote P (Env.append env tail) = e.denote P env := by
  simpa using congrArg Run.value (e.weakenTail_run P env tail)

end Signatures.Runtime
