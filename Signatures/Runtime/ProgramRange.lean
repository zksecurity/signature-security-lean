import Signatures.Runtime.NaturalRange
import Signatures.Runtime.Machine

/-! Nat/Fin ranges through stateful, response-adaptive programs. Handler
obligations concern actual supported replies and state transitions. They must
be discharged for the concrete handlers; arbitrary oracles cannot be assumed
to return bounded natural numbers. -/

open OracleComp OracleSpec

namespace Signatures.Runtime.NaturalRange

variable {F G₁ G₂ K M : Type}
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]

theorem args_bound (cost : PrimitiveCosts) {Γ Δ : List (Ty CryptoAtom)}
    (args : Args CryptoOp Γ Δ) (bits : Nat) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (he : EnvBound bits env) :
    EnvBound (bits + (args.run (arithmetic F G₁ G₂ K M cost) env).steps)
      (args.run (arithmetic F G₁ G₂ K M cost) env).value := by
  let P := arithmetic F G₁ G₂ K M cost
  change EnvBound (bits + (args.run P env).steps) (args.run P env).value
  induction args with
  | nil => trivial
  | cons e args ih =>
    have hh := expr_bound cost e bits env he
    change ValueBound (bits + (e.run P env).steps) (e.run P env).value at hh
    have ht := ih
    exact ⟨value_mono (by simp only [Args.run]; omega) _ hh,
      env_mono (by simp only [Args.run]; omega) _ ht⟩

def ArgsBound (cost : PrimitiveCosts) (width : Nat) {Γ Δ : List (Ty CryptoAtom)} :
    Args CryptoOp Γ Δ → Env (cryptoBase F G₁ G₂ K M) Γ → Prop
  | .nil, _ => True
  | .cons e rest, env => ExprBound cost width e env ∧ ArgsBound cost width rest env

theorem args_trace_bound (cost : PrimitiveCosts) {Γ Δ : List (Ty CryptoAtom)}
    (args : Args CryptoOp Γ Δ) (bits width : Nat) (env : Env (cryptoBase F G₁ G₂ K M) Γ)
    (he : EnvBound bits env)
    (hb : bits + (args.run (arithmetic F G₁ G₂ K M cost) env).steps ≤ width) :
    ArgsBound cost width args env := by
  induction args with
  | nil => trivial
  | cons e args ih =>
    exact ⟨expr_trace_bound cost e bits width env he (by simp only [Args.run] at hb; omega),
      ih (by simp only [Args.run] at hb; omega)⟩

variable {I S : Type} {spec : OracleSpec I}

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
private theorem repeat_bound {a : Ty CryptoAtom} (StateBound : Nat → S → Prop)
    (hm : ∀ {d e}, d ≤ e → ∀ s, StateBound d s → StateBound e s)
    (step : a.Value (cryptoBase F G₁ G₂ K M) → StateT S (OracleComp spec)
      (Run (a.Value (cryptoBase F G₁ G₂ K M)))) (base : Nat)
    (hstep : ∀ d, base ≤ d → ∀ x, ValueBound d x → ∀ s, StateBound d s →
      ∀ z ∈ support ((step x).run s),
        ValueBound (d + z.1.steps) z.1.value ∧ StateBound (d + z.1.steps) z.2)
    (n d : Nat) (hd : base ≤ d) (x : a.Value (cryptoBase F G₁ G₂ K M))
    (hx : ValueBound d x) (s : S) (hs : StateBound d s)
    (z : Run (a.Value (cryptoBase F G₁ G₂ K M)) × S)
    (hz : z ∈ support ((repeatRun step n x).run s)) :
    ValueBound (d + z.1.steps) z.1.value ∧ StateBound (d + z.1.steps) z.2 := by
  induction n generalizing d x s z with
  | zero =>
    simp only [repeatRun, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨value_mono (by dsimp; omega) _ hx, hm (by dsimp; omega) _ hs⟩
  | succ n ih =>
    simp only [repeatRun, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨⟨r, s₁⟩, hr, ⟨u, s₂⟩, hu, rfl⟩ := hz
    obtain ⟨hv, hs₁⟩ := hstep d hd x hx s hs (r, s₁) hr
    obtain ⟨hv', hs₂⟩ := ih (d + r.steps) (by omega) r.value hv s₁ hs₁ (u, s₂) hu
    exact ⟨value_mono (by dsimp; omega) _ hv', hm (by dsimp; omega) _ hs₂⟩

/-- A path's charged steps bound natural-value growth in both the returned
value and the handler state. This covers adaptive queries, loops, and calls. -/
theorem program_bound {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}
    (cost : PrimitiveCosts) (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd (StateT S (OracleComp spec)))
    (StateBound : Nat → S → Prop)
    (hm : ∀ {d e}, d ≤ e → ∀ s, StateBound d s → StateBound e s)
    (hh : ∀ {a b} (cmd : Cmd a b) (bits : Nat) (arg : a.Value (cryptoBase F G₁ G₂ K M)),
      ValueBound bits arg → ∀ s, StateBound bits s → ∀ z ∈ support ((H cmd arg).run s),
        ValueBound (bits + z.1.steps) z.1.value ∧ StateBound (bits + z.1.steps) z.2)
    {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} (code : Program CryptoOp Cmd Γ a)
    (bits : Nat) (env : Env (cryptoBase F G₁ G₂ K M) Γ) (he : EnvBound bits env)
    (s : S) (hs : StateBound bits s) (z : Run (a.Value (cryptoBase F G₁ G₂ K M)) × S)
    (hz : z ∈ support ((code.run (arithmetic F G₁ G₂ K M cost) H env).run s)) :
    ValueBound (bits + z.1.steps) z.1.value ∧ StateBound (bits + z.1.steps) z.2 := by
  let P := arithmetic F G₁ G₂ K M cost
  change z ∈ support ((code.run P H env).run s) at hz
  induction code generalizing bits s with
  | ret e =>
    simp only [Program.run, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨value_mono (by dsimp [P]; omega) _ (expr_bound cost e bits env he),
      hm (by dsimp; omega) _ hs⟩
  | query cmd arg =>
    simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
    have hv := expr_bound cost arg bits env he
    obtain ⟨hv', hs'⟩ := hh cmd (bits + (arg.run P env).steps) (arg.run P env).value hv
      s (hm (by omega) s hs) (r, s') hr
    exact ⟨value_mono (by dsimp; omega) _ hv', hm (by dsimp; omega) _ hs'⟩
  | bind code body ih ihbody =>
    simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨⟨r, s₁⟩, hr, ⟨u, s₂⟩, hu, rfl⟩ := hz
    obtain ⟨hv, hs₁⟩ := ih bits env he s hs (r, s₁) hr
    obtain ⟨hv', hs₂⟩ := ihbody (bits + r.steps) (r.value, env)
      ⟨hv, env_mono (by omega) _ he⟩ s₁ hs₁ (u, s₂) hu
    exact ⟨value_mono (by dsimp; omega) _ hv', hm (by dsimp; omega) _ hs₂⟩
  | branch cond yes no ihyes ihno =>
    by_cases hc : (cond.run P env).value = true
    · simp only [Program.run, hc, ite_true, StateT.run_bind, StateT.run_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
      obtain ⟨hv, hs'⟩ := ihyes bits env he s hs (r, s') hr
      exact ⟨value_mono (by dsimp; omega) _ hv, hm (by dsimp; omega) _ hs'⟩
    · simp only [Program.run, hc, Bool.false_eq_true, ite_false, StateT.run_bind,
        StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
      obtain ⟨hv, hs'⟩ := ihno bits env he s hs (r, s') hr
      exact ⟨value_mono (by dsimp; omega) _ hv, hm (by dsimp; omega) _ hs'⟩
  | loop count init body ih =>
    simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
    let d := bits + (init.run P env).steps
    have hd : bits ≤ d := by dsimp [d]; omega
    have hv := expr_bound cost init bits env he
    obtain ⟨hv', hs'⟩ := repeat_bound StateBound hm (fun acc => body.run P H (acc, env)) bits
      (fun k hk acc ha state hi out hout => ih k (acc, env)
        ⟨ha, env_mono hk _ he⟩ state hi out hout)
      (count.run P env).value d hd (init.run P env).value hv s (hm hd s hs) (r, s') hr
    exact ⟨value_mono (by dsimp [d] at *; omega) _ hv', hm (by dsimp [d] at *; omega) _ hs'⟩
  | call body args ih =>
    simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨⟨r, s'⟩, hr, rfl⟩ := hz
    obtain ⟨hv, hs'⟩ := ih (bits + (args.run P env).steps) (args.run P env).value
      (args_bound cost args bits env he) s (hm (by omega) s hs) (r, s') hr
    exact ⟨value_mono (by dsimp; omega) _ hv, hm (by dsimp; omega) _ hs'⟩

variable [SampleableType F]

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
/-- The closed machine's store effects preserve ranges. A uniform sampler must
charge enough steps for its result width; the abstract arithmetic model alone
does not impose this implementation obligation on arbitrary sampling prices. -/
theorem effects_bound (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n)) (store : Ty CryptoAtom)
    {a b : Ty CryptoAtom} (cmd : Machine.Effect store a b) (bits : Nat)
    (arg : a.Value (cryptoBase F G₁ G₂ K M)) (ha : ValueBound bits arg)
    (s : store.Value (cryptoBase F G₁ G₂ K M)) (hs : ValueBound bits s)
    (z : Run (b.Value (cryptoBase F G₁ G₂ K M)) × store.Value (cryptoBase F G₁ G₂ K M))
    (hz : z ∈ support ((Machine.effects sampling store cmd arg).run s)) :
    ValueBound (bits + z.1.steps) z.1.value ∧ ValueBound (bits + z.1.steps) z.2 := by
  cases cmd with
  | scalar =>
    simp only [Machine.effects, StateT.run, support_map, Set.mem_image] at hz
    obtain ⟨x, _, rfl⟩ := hz
    exact ⟨trivial, value_mono (by dsimp; omega) _ hs⟩
  | uniform n =>
    simp only [Machine.effects, StateT.run, support_map, Set.mem_image] at hz
    obtain ⟨x, _, rfl⟩ := hz
    refine ⟨?_, value_mono (by dsimp; omega) _ hs⟩
    exact (Nat.le_of_lt_succ x.isLt).trans_lt ((hsampling n).trans_le
      (Nat.pow_le_pow_right (by decide) (by dsimp; omega)))
  | read =>
    simp only [Machine.effects, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨value_mono (by dsimp; omega) _ hs, value_mono (by dsimp; omega) _ hs⟩
  | write =>
    simp only [Machine.effects, StateT.run, support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨trivial, value_mono (by dsimp; omega) _ ha⟩

theorem machine_bound (cost : PrimitiveCosts) (sampling : Machine.SamplingCosts)
    (hsampling : ∀ n, n < 2^(sampling.uniform n)) {inputs : List (Ty CryptoAtom)} {output : Ty CryptoAtom}
    (code : Machine.Code inputs output) (bits : Nat) (env : Env (cryptoBase F G₁ G₂ K M) inputs)
    (he : EnvBound bits env) (z : Run (output.Value (cryptoBase F G₁ G₂ K M)))
    (hz : z ∈ support (code.run cost sampling env)) : ValueBound (bits + z.steps) z.value := by
  let P := arithmetic F G₁ G₂ K M cost
  simp only [Machine.Code.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨⟨r, s⟩, hr, rfl⟩ := hz
  have hinit := expr_bound cost code.init bits env he
  have h := program_bound cost (Machine.effects sampling code.store)
    (fun k state => ValueBound k state) (fun h state hi => value_mono h state hi)
    (effects_bound sampling hsampling code.store) code.body
    (bits + (code.init.run P env).steps) env (env_mono (by omega) env he)
    (code.init.run P env).value hinit (r, s) hr
  exact value_mono (by dsimp [P]; omega) _ h.1

end Signatures.Runtime.NaturalRange
