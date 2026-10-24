import Proofs.Runtime.ProgramRange

/-! Range checks for every reached expression and returned oracle reply.
These are derived from an end-to-end source budget, including adaptive replies,
procedure calls, and each counted-loop iteration. Oracle response types must be
nonempty so a terminal budget cannot conceal an arbitrarily expensive dead end. -/

namespace Signatures.Runtime.NaturalRange

open OracleComp

variable {I S A : Type} {spec : OracleSpec I}

def RepeatTrace (check : A → S → Prop) (step : A → StateT S (OracleComp spec) (Run A)) :
    Nat → A → S → Prop
  | 0, _, _ => True
  | n+1, x, state => check x state ∧
    ∀ out ∈ support ((step x).run state), RepeatTrace check step n out.1.value out.2

variable {F G₁ G₂ K M : Type}
  [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
  {Cmd : Ty CryptoAtom → Ty CryptoAtom → Type}

def ProgramTrace (cost : PrimitiveCosts) (width : Nat)
    (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd (StateT S (OracleComp spec)))
    {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} :
    Program CryptoOp Cmd Γ a → Env (cryptoBase F G₁ G₂ K M) Γ → S → Prop
  | .ret e, env, _ => ExprBound cost width e env
  | .query cmd arg, env, state => ExprBound cost width arg env ∧
    ∀ out ∈ support ((H cmd (arg.run (arithmetic F G₁ G₂ K M cost) env).value).run state),
      ValueBound width out.1.value
  | .bind first body, env, state => ProgramTrace cost width H first env state ∧
    ∀ out ∈ support ((first.run (arithmetic F G₁ G₂ K M cost) H env).run state),
      ProgramTrace cost width H body (out.1.value, env) out.2
  | .branch cond yes no, env, state => ExprBound cost width cond env ∧
    if (cond.run (arithmetic F G₁ G₂ K M cost) env).value then
      ProgramTrace cost width H yes env state else ProgramTrace cost width H no env state
  | .loop count init body, env, state =>
    ExprBound cost width count env ∧ ExprBound cost width init env ∧
      RepeatTrace (fun acc state => ProgramTrace cost width H body (acc, env) state)
        (fun acc => body.run (arithmetic F G₁ G₂ K M cost) H (acc, env))
        (count.run (arithmetic F G₁ G₂ K M cost) env).value
        (init.run (arithmetic F G₁ G₂ K M cost) env).value state
  | .call body args, env, state => ArgsBound cost width args env ∧
    ProgramTrace cost width H body (args.run (arithmetic F G₁ G₂ K M cost) env).value state

variable [∀ q, Nonempty (spec.Range q)]

omit [Field F] [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M] in
private theorem repeat_trace_bound {a : Ty CryptoAtom}
    (StateBound : Nat → S → Prop) (base width : Nat)
    (step : a.Value (cryptoBase F G₁ G₂ K M) → StateT S (OracleComp spec)
      (Run (a.Value (cryptoBase F G₁ G₂ K M))))
    (check : a.Value (cryptoBase F G₁ G₂ K M) → S → Prop)
    (hgrowth : ∀ d, base ≤ d → ∀ x, ValueBound d x → ∀ state, StateBound d state →
      ∀ out ∈ support ((step x).run state),
        ValueBound (d+out.1.steps) out.1.value ∧ StateBound (d+out.1.steps) out.2)
    (hcheck : ∀ d, base ≤ d → ∀ x, ValueBound d x → ∀ state, StateBound d state →
      (∀ out ∈ support ((step x).run state), d+out.1.steps ≤ width) → check x state)
    (n d : Nat) (hd : base ≤ d) (x : a.Value (cryptoBase F G₁ G₂ K M))
    (hx : ValueBound d x) (state : S) (hs : StateBound d state)
    (hb : ∀ out ∈ support ((repeatRun step n x).run state), d+out.1.steps ≤ width) :
    RepeatTrace check step n x state := by
  induction n generalizing d x state with
  | zero => trivial
  | succ n ih =>
    have htotal r (hr : r ∈ support ((step x).run state)) z
        (hz : z ∈ support ((repeatRun step n r.1.value).run r.2)) :
        d + (r.1.steps+z.1.steps+2) ≤ width := by
      apply hb (⟨z.1.value, r.1.steps+z.1.steps+2⟩, z.2)
      simp only [repeatRun, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨r, hr, z, hz, rfl⟩
    constructor
    · apply hcheck d hd x hx state hs
      intro out hout
      obtain ⟨last, hlast⟩ := support_nonempty ((repeatRun step n out.1.value).run out.2)
      have h := htotal out hout last hlast
      omega
    · intro out hout
      obtain ⟨hv, hs'⟩ := hgrowth d hd x hx state hs out hout
      apply ih (d+out.1.steps) (by omega) out.1.value hv out.2 hs'
      intro last hlast
      have h := htotal out hout last hlast
      omega

/-- A total source budget bounds every executed expression, not just the final
result. Handler growth is checked on actual supported replies and states. -/
theorem program_trace_bound
    (cost : PrimitiveCosts)
    (H : HandlerM (cryptoBase F G₁ G₂ K M) Cmd (StateT S (OracleComp spec)))
    (StateBound : Nat → S → Prop)
    (hm : ∀ {d e}, d ≤ e → ∀ state, StateBound d state → StateBound e state)
    (hh : ∀ {a b} (cmd : Cmd a b) (bits : Nat) (arg : a.Value (cryptoBase F G₁ G₂ K M)),
      ValueBound bits arg → ∀ state, StateBound bits state → ∀ out ∈ support ((H cmd arg).run state),
        ValueBound (bits+out.1.steps) out.1.value ∧ StateBound (bits+out.1.steps) out.2)
    {Γ : List (Ty CryptoAtom)} {a : Ty CryptoAtom} (code : Program CryptoOp Cmd Γ a)
    (bits width : Nat) (env : Env (cryptoBase F G₁ G₂ K M) Γ) (he : EnvBound bits env)
    (state : S) (hs : StateBound bits state)
    (hb : ∀ out ∈ support ((code.run (arithmetic F G₁ G₂ K M cost) H env).run state),
      bits+out.1.steps ≤ width) : ProgramTrace cost width H code env state := by
  let P := arithmetic F G₁ G₂ K M cost
  change ∀ out ∈ support ((code.run P H env).run state), bits+out.1.steps ≤ width at hb
  induction code generalizing bits state with
  | ret e =>
    have hc := hb (⟨(e.run P env).value, (e.run P env).steps+1⟩, state)
      (by simp [Program.run])
    exact expr_trace_bound cost e bits width env he
      (by change bits+(e.run P env).steps ≤ width; dsimp only at hc; omega)
  | query cmd arg =>
    obtain ⟨out, hout⟩ := support_nonempty ((H cmd (arg.run P env).value).run state)
    have hc := hb (⟨out.1.value, (arg.run P env).steps+out.1.steps+1⟩, out.2) (by
      simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨out, hout, rfl⟩)
    constructor
    · exact expr_trace_bound cost arg bits width env he
        (by change bits+(arg.run P env).steps ≤ width; dsimp only at hc; omega)
    · intro out hout
      have htotal := hb (⟨out.1.value, (arg.run P env).steps+out.1.steps+1⟩, out.2) (by
        simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff]
        exact ⟨out, hout, rfl⟩)
      have hv := (hh cmd (bits+(arg.run P env).steps) (arg.run P env).value
        (expr_bound cost arg bits env he) state (hm (by omega) state hs) out hout).1
      exact value_mono (by dsimp only at htotal; omega) _ hv
  | bind first body ihfirst ihbody =>
    have htotal r (hr : r ∈ support ((first.run P H env).run state)) out
        (hout : out ∈ support ((body.run P H (r.1.value, env)).run r.2)) :
        bits + (r.1.steps+out.1.steps+1) ≤ width := by
      apply hb (⟨out.1.value, r.1.steps+out.1.steps+1⟩, out.2)
      simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨r, hr, out, hout, rfl⟩
    constructor
    · apply ihfirst bits env he state hs
      intro r hr
      obtain ⟨out, hout⟩ := support_nonempty ((body.run P H (r.1.value, env)).run r.2)
      have h := htotal r hr out hout
      omega
    · intro r hr
      obtain ⟨hv, hs'⟩ := program_bound cost H StateBound hm hh first bits env he state hs r hr
      apply ihbody (bits+r.1.steps) (r.1.value, env)
        ⟨hv, env_mono (by omega) env he⟩ r.2 hs'
      intro out hout
      have h := htotal r hr out hout
      omega
  | branch cond yes no ihyes ihno =>
    cases hc : (cond.run P env).value with
    | false =>
      have htotal out (hout : out ∈ support ((no.run P H env).run state)) :
          bits+((cond.run P env).steps+out.1.steps+1) ≤ width := by
        apply hb (⟨out.1.value, (cond.run P env).steps+out.1.steps+1⟩, out.2)
        simp only [Program.run, hc, Bool.false_eq_true, ite_false, StateT.run_bind,
          StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨out, hout, rfl⟩
      change ExprBound cost width cond env ∧ _
      constructor
      · obtain ⟨out, hout⟩ := support_nonempty ((no.run P H env).run state)
        have h := htotal out hout
        exact expr_trace_bound cost cond bits width env he
          (by change bits+(cond.run P env).steps ≤ width; omega)
      · change if (cond.run P env).value then _ else _
        rw [hc]
        apply ihno bits env he state hs
        intro out hout
        have h := htotal out hout
        omega
    | true =>
      have htotal out (hout : out ∈ support ((yes.run P H env).run state)) :
          bits+((cond.run P env).steps+out.1.steps+1) ≤ width := by
        apply hb (⟨out.1.value, (cond.run P env).steps+out.1.steps+1⟩, out.2)
        simp only [Program.run, hc, ite_true, StateT.run_bind,
          StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
        exact ⟨out, hout, rfl⟩
      change ExprBound cost width cond env ∧ _
      constructor
      · obtain ⟨out, hout⟩ := support_nonempty ((yes.run P H env).run state)
        have h := htotal out hout
        exact expr_trace_bound cost cond bits width env he
          (by change bits+(cond.run P env).steps ≤ width; omega)
      · change if (cond.run P env).value then _ else _
        rw [hc]
        apply ihyes bits env he state hs
        intro out hout
        have h := htotal out hout
        omega
  | loop count init body ih =>
    let step := fun acc => body.run P H (acc, env)
    have htotal out (hout : out ∈ support
        ((repeatRun step (count.run P env).value (init.run P env).value).run state)) :
        bits+((count.run P env).steps+(init.run P env).steps+out.1.steps+1) ≤ width := by
      apply hb (⟨out.1.value, (count.run P env).steps+(init.run P env).steps+out.1.steps+1⟩, out.2)
      simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨out, hout, rfl⟩
    obtain ⟨out, hout⟩ := support_nonempty
      ((repeatRun step (count.run P env).value (init.run P env).value).run state)
    have h := htotal out hout
    refine ⟨expr_trace_bound cost count bits width env he
      (by change bits+(count.run P env).steps ≤ width; omega),
      expr_trace_bound cost init bits width env he
      (by change bits+(init.run P env).steps ≤ width; omega), ?_⟩
    apply repeat_trace_bound StateBound bits width step
      (fun acc state => ProgramTrace cost width H body (acc, env) state)
      (fun d hd acc ha state hs =>
        program_bound cost H StateBound hm hh body d (acc, env)
          ⟨ha, env_mono hd env he⟩ state hs)
      (fun d hd acc ha state hs hb => ih d (acc, env) ⟨ha, env_mono hd env he⟩ state hs hb)
      _ (bits+(init.run P env).steps) (by omega) _ (expr_bound cost init bits env he)
      state (hm (by omega) state hs)
    intro last hlast
    have h := htotal last hlast
    omega
  | call body args ih =>
    have htotal out (hout : out ∈ support ((body.run P H (args.run P env).value).run state)) :
        bits+((args.run P env).steps+out.1.steps+2) ≤ width := by
      apply hb (⟨out.1.value, (args.run P env).steps+out.1.steps+2⟩, out.2)
      simp only [Program.run, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
        support_pure, Set.mem_singleton_iff]
      exact ⟨out, hout, rfl⟩
    constructor
    · obtain ⟨out, hout⟩ := support_nonempty ((body.run P H (args.run P env).value).run state)
      have h := htotal out hout
      exact args_trace_bound cost args bits width env he
        (by change bits+(args.run P env).steps ≤ width; omega)
    · apply ih (bits+(args.run P env).steps) (args.run P env).value
        (args_bound cost args bits env he) state (hm (by omega) state hs)
      intro out hout
      have h := htotal out hout
      omega

end Signatures.Runtime.NaturalRange
