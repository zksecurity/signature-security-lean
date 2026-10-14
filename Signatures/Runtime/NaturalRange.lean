import Signatures.Runtime.Arithmetic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-! Natural-number range growth in the actual first-order arithmetic language.
Bounds inspect Nat and Fin leaves, including leaves nested in pairs/lists.
Field/group/key/message leaves are separate fixed-codec obligations. -/

namespace Signatures.Runtime.NaturalRange

variable {F G₁ G₂ K M : Type}

def ValueBound (bits : Nat) : {t : Ty CryptoAtom} → t.Value (cryptoBase F G₁ G₂ K M) → Prop
  | .nat, n => n < 2^bits
  | .atom (.fin _), n => n.val < 2^bits
  | .pair _ _, x => ValueBound bits x.1 ∧ ValueBound bits x.2
  | .list _, xs => ∀ x ∈ xs, ValueBound bits x
  | _, _ => True

def EnvBound (bits : Nat) : {Γ : List (Ty CryptoAtom)} → Env (cryptoBase F G₁ G₂ K M) Γ → Prop
  | [], _ => True
  | _ :: _, env => ValueBound bits env.1 ∧ EnvBound bits env.2

theorem value_mono {b c : Nat} (h : b ≤ c) {t : Ty CryptoAtom}
    (x : t.Value (cryptoBase F G₁ G₂ K M)) (hx : ValueBound b x) : ValueBound c x := by
  have hp : 2^b ≤ 2^c := Nat.pow_le_pow_right (by decide) h
  induction t with
  | atom a => cases a <;> first | exact hx.trans_le hp | trivial
  | nat => exact hx.trans_le hp
  | unit | bool => trivial
  | pair a b iha ihb => exact ⟨iha _ hx.1, ihb _ hx.2⟩
  | list a ih => exact fun x hxmem => ih x (hx x hxmem)

theorem env_mono {b c : Nat} (h : b ≤ c) {Γ : List (Ty CryptoAtom)}
    (env : Env (cryptoBase F G₁ G₂ K M) Γ) (he : EnvBound b env) : EnvBound c env := by
  induction Γ with
  | nil => trivial
  | cons a Γ ih => exact ⟨value_mono h _ he.1, ih env.2 he.2⟩

theorem var_bound (bits : Nat) {Γ : List (Ty CryptoAtom)} {t : Ty CryptoAtom}
    (v : Var Γ t) (env : Env (cryptoBase F G₁ G₂ K M) Γ) (he : EnvBound bits env) :
    ValueBound bits (v.get env) := by
  induction v with
  | here => exact he.1
  | there v ih => exact ih env.2 he.2

variable [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

/-- Of all primitives, only natural addition can increase a natural's bit bound,
and it increases it by at most one. Large Fin moduli do not enlarge their input. -/
theorem op_bound (cost : PrimitiveCosts) (bits : Nat) {a b : Ty CryptoAtom}
    (op : CryptoOp a b) (x : a.Value (cryptoBase F G₁ G₂ K M)) (hx : ValueBound bits x) :
    ValueBound (bits + 1) ((arithmetic F G₁ G₂ K M cost).execute op x) := by
  have hp : 2^bits ≤ 2^(bits+1) := Nat.pow_le_pow_right (by decide) (by omega)
  cases op with
  | natAdd =>
    change x.1 + x.2 < 2^(bits+1)
    have h₁ : x.1 < 2^bits := hx.1
    have h₂ : x.2 < 2^bits := hx.2
    simpa only [Nat.pow_succ, Nat.mul_two] using Nat.add_lt_add h₁ h₂
  | natSub => exact (Nat.sub_le _ _).trans_lt (hx.1.trans_le hp)
  | finVal n => exact hx.trans_le hp
  | finZero n => exact Nat.two_pow_pos _
  | finOfNat n => exact (Nat.mod_le _ _).trans_lt (hx.trans_le hp)
  | _ => trivial

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
private theorem fold_bound {a b : Ty CryptoAtom}
    (step : a.Value (cryptoBase F G₁ G₂ K M) → b.Value (cryptoBase F G₁ G₂ K M) →
      Run (b.Value (cryptoBase F G₁ G₂ K M))) (base : Nat)
    (hs : ∀ d, base ≤ d → ∀ x acc, ValueBound d x → ValueBound d acc →
      ValueBound (d + (step x acc).steps) (step x acc).value)
    (xs : List (a.Value (cryptoBase F G₁ G₂ K M))) (d : Nat) (hd : base ≤ d)
    (hx : ∀ x ∈ xs, ValueBound d x) (acc : b.Value (cryptoBase F G₁ G₂ K M))
    (ha : ValueBound d acc) :
    ValueBound (d + (foldRun step xs acc).steps) (foldRun step xs acc).value := by
  induction xs generalizing d acc with
  | nil => exact value_mono (by omega) _ ha
  | cons x xs ih =>
    have hh := hs d hd x acc (hx x (by simp)) ha
    have ht := ih (d + (step x acc).steps) (by omega)
      (fun y hy => value_mono (by omega) y (hx y (by simp [hy]))) (step x acc).value hh
    exact value_mono (by simp only [foldRun]; omega) _ ht

/-- The output's natural leaves fit in the initial width plus the charged local
execution steps. This is about the existing Expr.run, not an assumed growth rate. -/
theorem expr_bound (cost : PrimitiveCosts) {Γ : List (Ty CryptoAtom)} {t : Ty CryptoAtom}
    (e : Expr CryptoOp Γ t) (bits : Nat) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (he : EnvBound bits env) :
    ValueBound (bits + (e.run (arithmetic F G₁ G₂ K M cost) env).steps)
      (e.run (arithmetic F G₁ G₂ K M cost) env).value := by
  let P := arithmetic F G₁ G₂ K M cost
  change ValueBound (bits + (e.run P env).steps) (e.run P env).value
  induction e generalizing bits with
  | var v => exact value_mono (by omega) _ (var_bound bits v env he)
  | unit | bool b => trivial
  | nil => simp [Expr.run, ValueBound]
  | nat n =>
    exact n.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (by simp [Expr.run]; omega))
  | pair l r ihl ihr =>
    exact ⟨value_mono (by simp only [Expr.run]; omega) _ (ihl bits env he),
      value_mono (by simp only [Expr.run]; omega) _ (ihr bits env he)⟩
  | fst e ih => exact value_mono (by simp only [Expr.run]; omega) _ (ih bits env he).1
  | snd e ih => exact value_mono (by simp only [Expr.run]; omega) _ (ih bits env he).2
  | cons x xs ihx ihxs =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact value_mono (by simp only [Expr.run]; omega) _ (ihx bits env he)
    · exact value_mono (by simp only [Expr.run]; omega) _ (ihxs bits env he y hy)
  | branch c yes no ihc ihy ihn =>
    simp only [Expr.run]
    split
    · exact value_mono (by omega) _ (ihy bits env he)
    · exact value_mono (by omega) _ (ihn bits env he)
  | letE e body ihe ihbody =>
    have hval := ihe bits env he
    have henv := env_mono (show bits ≤ bits + (e.run P env).steps by omega) env he
    have hb := ihbody (bits + (e.run P env).steps) ((e.run P env).value, env) ⟨hval, henv⟩
    exact value_mono (by simp only [Expr.run]; omega) _ hb
  | op op e ih =>
    have hv := op_bound cost (bits + (e.run P env).steps) op (e.run P env).value (ih bits env he)
    exact value_mono (by simp only [Expr.run]; omega) _ hv
  | fold xs init body ihxs ihinit ihbody =>
    let d := bits + (xs.run P env).steps + (init.run P env).steps
    have hxs : ∀ x ∈ (xs.run P env).value, ValueBound d x :=
      fun x hx => value_mono (by dsimp [d]; omega) x (ihxs bits env he x hx)
    have hi : ValueBound d (init.run P env).value :=
      value_mono (by dsimp [d]; omega) _ (ihinit bits env he)
    have hb := fold_bound (fun x acc => body.run P (x, acc, env)) d
      (fun k hk x acc hx ha => ihbody k (x, acc, env)
        ⟨hx, ha, env_mono (by dsimp [d] at hk; omega) env he⟩)
      (xs.run P env).value d le_rfl hxs (init.run P env).value hi
    exact value_mono (by simp only [Expr.run]; dsimp only [d]; omega) _ hb

/-- Check each accumulator transition on its actual execution path. -/
def foldChecks {α β : Type} (check : α → β → Prop) (step : α → β → Run β) : List α → β → Prop
  | [], _ => True
  | x :: xs, acc => check x acc ∧ foldChecks check step xs (step x acc).value

/-- All natural values produced by local evaluation fit, including discarded
intermediates and every executed fold iteration, not just the final result. -/
def ExprBound (cost : PrimitiveCosts) (width : Nat) {Γ : List (Ty CryptoAtom)} {t : Ty CryptoAtom} :
    Expr CryptoOp Γ t → Env (cryptoBase F G₁ G₂ K M) Γ → Prop
  | .var v, env => ValueBound width (v.get env)
  | .unit, _ | .bool _, _ | .nil, _ => True
  | .nat n, _ => n < 2^width
  | .pair l r, env => ExprBound cost width l env ∧ ExprBound cost width r env
  | .fst e, env | .snd e, env => ExprBound cost width e env
  | .cons x xs, env => ExprBound cost width x env ∧ ExprBound cost width xs env
  | .branch c yes no, env => ExprBound cost width c env ∧
      if (c.run (arithmetic F G₁ G₂ K M cost) env).value = true then ExprBound cost width yes env
      else ExprBound cost width no env
  | .letE e body, env => ExprBound cost width e env ∧
      ExprBound cost width body ((e.run (arithmetic F G₁ G₂ K M cost) env).value, env)
  | .op op e, env => ExprBound cost width e env ∧ ValueBound width
      ((arithmetic F G₁ G₂ K M cost).execute op (e.run (arithmetic F G₁ G₂ K M cost) env).value)
  | .fold xs init body, env => ExprBound cost width xs env ∧ ExprBound cost width init env ∧
      foldChecks (fun x acc => ExprBound cost width body (x, acc, env))
        (fun x acc => body.run (arithmetic F G₁ G₂ K M cost) (x, acc, env))
        (xs.run (arithmetic F G₁ G₂ K M cost) env).value
        (init.run (arithmetic F G₁ G₂ K M cost) env).value

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
private theorem fold_checks_bound {a b : Ty CryptoAtom}
    (step : a.Value (cryptoBase F G₁ G₂ K M) → b.Value (cryptoBase F G₁ G₂ K M) →
      Run (b.Value (cryptoBase F G₁ G₂ K M))) (check : a.Value (cryptoBase F G₁ G₂ K M) →
      b.Value (cryptoBase F G₁ G₂ K M) → Prop) (base width : Nat)
    (hg : ∀ d, base ≤ d → ∀ x acc, ValueBound d x → ValueBound d acc →
      ValueBound (d + (step x acc).steps) (step x acc).value)
    (hc : ∀ d, base ≤ d → ∀ x acc, ValueBound d x → ValueBound d acc →
      d + (step x acc).steps ≤ width → check x acc)
    (xs : List (a.Value (cryptoBase F G₁ G₂ K M))) (d : Nat) (hd : base ≤ d)
    (hx : ∀ x ∈ xs, ValueBound d x) (acc : b.Value (cryptoBase F G₁ G₂ K M))
    (ha : ValueBound d acc) (hb : d + (foldRun step xs acc).steps ≤ width) :
    foldChecks check step xs acc := by
  induction xs generalizing d acc with
  | nil => trivial
  | cons x xs ih =>
    have hh := hx x (by simp)
    have hv := hg d hd x acc hh ha
    refine ⟨hc d hd x acc hh ha (by simp only [foldRun] at hb; omega), ?_⟩
    exact ih (d + (step x acc).steps) (by omega)
      (fun y hy => value_mono (by omega) y (hx y (by simp [hy]))) (step x acc).value hv
      (by simp only [foldRun] at hb; omega)

/-- A local execution budget supplies a common word width for every intermediate
Nat/Fin value along that execution. No overflow assumption is supplied per node. -/
theorem expr_trace_bound (cost : PrimitiveCosts) {Γ : List (Ty CryptoAtom)} {t : Ty CryptoAtom}
    (e : Expr CryptoOp Γ t) (bits width : Nat) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (he : EnvBound bits env) (hb : bits + (e.run (arithmetic F G₁ G₂ K M cost) env).steps ≤ width) :
    ExprBound cost width e env := by
  let P := arithmetic F G₁ G₂ K M cost
  change bits + (e.run P env).steps ≤ width at hb
  induction e generalizing bits with
  | var v => exact value_mono (by omega) _ (var_bound bits v env he)
  | unit | bool b | nil => trivial
  | nat n =>
    exact n.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by decide) (by simp only [Expr.run] at hb; omega))
  | pair l r ihl ihr =>
    exact
      ⟨ihl bits env he (by simp only [Expr.run] at hb; omega),
       ihr bits env he (by simp only [Expr.run] at hb; omega)⟩
  | fst e ih | snd e ih => exact ih bits env he (by simp only [Expr.run] at hb; omega)
  | cons x xs ihx ihxs =>
    exact
      ⟨ihx bits env he (by simp only [Expr.run] at hb; omega),
       ihxs bits env he (by simp only [Expr.run] at hb; omega)⟩
  | branch c yes no ihc ihy ihn =>
    by_cases hc : (c.run P env).value = true
    · simp only [ExprBound, show arithmetic F G₁ G₂ K M cost = P from rfl, hc, ite_true]
      simp only [Expr.run, hc, ite_true] at hb
      exact ⟨ihc bits env he (by omega), ihy bits env he (by omega)⟩
    · simp only [ExprBound, show arithmetic F G₁ G₂ K M cost = P from rfl, hc, Bool.false_eq_true, ite_false]
      simp only [Expr.run, hc, Bool.false_eq_true, ite_false] at hb
      exact ⟨ihc bits env he (by omega), ihn bits env he (by omega)⟩
  | letE e body ihe ihbody =>
    have hv := expr_bound cost e bits env he
    have henv := env_mono (show bits ≤ bits + (e.run P env).steps by omega) env he
    refine ⟨ihe bits env he (by simp only [Expr.run] at hb; omega), ?_⟩
    exact ihbody (bits + (e.run P env).steps) ((e.run P env).value, env) ⟨hv, henv⟩
      (by simp only [Expr.run] at hb; omega)
  | op op e ih =>
    have hv := expr_bound cost (Expr.op op e) bits env he
    exact ⟨ih bits env he (by simp only [Expr.run] at hb; omega), value_mono hb _ hv⟩
  | fold xs init body ihxs ihinit ihbody =>
    let d := bits + (xs.run P env).steps + (init.run P env).steps
    have hxs : ∀ x ∈ (xs.run P env).value, ValueBound d x :=
      fun x hx => value_mono (by dsimp [d, P]; omega) x (expr_bound cost xs bits env he x hx)
    have hi : ValueBound d (init.run P env).value :=
      value_mono (by dsimp [d, P]; omega) _ (expr_bound cost init bits env he)
    refine ⟨ihxs bits env he (by simp only [Expr.run] at hb; omega),
      ihinit bits env he (by simp only [Expr.run] at hb; omega), ?_⟩
    apply fold_checks_bound (fun x acc => body.run P (x, acc, env)) _ d width
      (fun k hk x acc hx ha => expr_bound cost body k (x, acc, env)
        ⟨hx, ha, env_mono (by dsimp [d] at hk; omega) env he⟩)
      (fun k hk x acc hx ha hstep => ihbody k (x, acc, env)
        ⟨hx, ha, env_mono (by dsimp [d] at hk; omega) env he⟩ hstep)
      (xs.run P env).value d le_rfl hxs (init.run P env).value hi
    simp only [Expr.run] at hb
    dsimp only [d]
    omega

end Signatures.Runtime.NaturalRange
