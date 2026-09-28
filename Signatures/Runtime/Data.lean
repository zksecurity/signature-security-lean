import Signatures.Runtime.Language

/-! Loading fixed first-order data. Atomic values are primitive words in the arithmetic
model; list and tuple structure is traversed and reconstructed, and natural literals pay
their unary load cost. No data field is executable host-language code. -/

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type}

def Ty.load : (a : Ty Atom) → a.Value base → Run (a.Value base)
  | .atom _, x => ⟨x, 1⟩
  | .unit, x => ⟨x, 1⟩
  | .bool, x => ⟨x, 1⟩
  | .nat, n => ⟨n, n + 1⟩
  | .pair a b, x =>
      let l := a.load x.1
      let r := b.load x.2
      ⟨(l.value, r.value), l.steps + r.steps + 1⟩
  | .list a, xs => xs.foldr (fun x tail =>
      let head := a.load x
      ⟨head.value :: tail.value, head.steps + tail.steps + 1⟩) ⟨[], 1⟩

@[simp] theorem Ty.load_value (a : Ty Atom) (x : a.Value base) : (a.load x).value = x := by
  induction a with
  | atom a => rfl
  | unit => rfl
  | bool => rfl
  | nat => rfl
  | pair a b ihl ihr => simp [load, ihl, ihr]
  | list a ih =>
      induction x with
      | nil => rfl
      | cons x xs iht => simpa [load, ih] using congrArg (List.cons x) iht

def Env.load : {Γ : List (Ty Atom)} → Env base Γ → Run (Env base Γ)
  | [], _ => ⟨(), 1⟩
  | a :: _, env =>
      let head := a.load env.1
      let tail := Env.load env.2
      ⟨(head.value, tail.value), head.steps + tail.steps + 1⟩

@[simp] theorem Env.load_value {Γ : List (Ty Atom)} (env : Env base Γ) :
    (Env.load env).value = env := by
  induction Γ with
  | nil => cases env; rfl
  | cons a Γ ih => simp [load, ih]

def Env.append {Γ Δ : List (Ty Atom)} (env : Env base Γ) (tail : Env base Δ) : Env base (Γ ++ Δ) :=
  match Γ, env with
  | [], _ => tail
  | _ :: _, (x, xs) => (x, Env.append xs tail)

/-- Copy the input register spine, sharing the already-loaded immutable data tail. -/
def Env.attach {Γ Δ : List (Ty Atom)} (env : Env base Γ) (tail : Env base Δ) : Run (Env base (Γ ++ Δ)) :=
  match Γ, env with
  | [], _ => ⟨tail, 1⟩
  | _ :: _, (x, xs) =>
      let r := Env.attach xs tail
      ⟨(x, r.value), r.steps + 1⟩

@[simp] theorem Env.attach_value {Γ Δ : List (Ty Atom)} (env : Env base Γ) (tail : Env base Δ) :
    (Env.attach env tail).value = Env.append env tail := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih => exact congrArg (Prod.mk env.1) (ih env.2)

@[simp] theorem Env.attach_steps {Γ Δ : List (Ty Atom)} (env : Env base Γ) (tail : Env base Δ) :
    (Env.attach env tail).steps = Γ.length + 1 := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih =>
      change (Env.attach env.2 tail).steps + 1 = Γ.length + 1 + 1
      rw [ih]

end Signatures.Runtime
