import Signatures.Runtime.Composition

/-!
# Source implementation budgets and runtime substitution

A source budget uniformly prices the capabilities of a first-order adversary program. It
includes all its local runtime, not just its oracle interactions. The target theorem derives
an implemented runtime bound from that source certificate and per-handler certificates.
Neither a time bound for the whole simulator nor one for the finished solver is assumed.
-/

open OracleComp OracleSpec

namespace Signatures.Runtime

variable {Atom : Type} {base : Atom → Type} {Op Cmd : Ty Atom → Ty Atom → Type}

structure Request (base : Atom → Type) (Cmd : Ty Atom → Ty Atom → Type) where
  input : Ty Atom
  output : Ty Atom
  instruction : Cmd input output
  argument : input.Value base

/-- A reply contract cannot justify bounds by making a request's response type empty. -/
structure ReplyContract (base : Atom → Type) (Cmd : Ty Atom → Ty Atom → Type) where
  allows : {a b : Ty Atom} → Cmd a b → a.Value base → b.Value base → Prop
  responds : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base), ∃ y, allows cmd arg y

def requestSpec (contract : ReplyContract base Cmd) : OracleSpec (Request base Cmd) :=
  fun q => {y : q.output.Value base // contract.allows q.instruction q.argument y}

def pricedRequests (contract : ReplyContract base Cmd)
    (fee : {a b : Ty Atom} → Cmd a b → Nat) : Handler base Cmd (requestSpec contract) :=
  fun {a b} cmd arg => do
    let y ← (liftM ((requestSpec contract).query ⟨a, b, cmd, arg⟩) :
      OracleComp (requestSpec contract) {y : b.Value base // contract.allows cmd arg y})
    pure ⟨y.val, fee cmd⟩

variable {K : Type} [Fintype K]

/-- A source implementation budget, uniform in every nonnegative capability price.
Taking all prices zero isolates local computation; positive prices additionally account for
every request on every contract-conforming response path, including repeated requests. -/
def SourceBudget (P : Primitives base Op) (contract : ReplyContract base Cmd)
    (kind : {a b : Ty Atom} → Cmd a b → K) {Γ a} (code : Program Op Cmd Γ a)
    (env : Env base Γ) (localTime : Nat) (queries : K → Nat) : Prop :=
  ∀ price : K → Nat, ∀ z ∈ support (code.run P (pricedRequests contract (fun cmd => price (kind cmd))) env),
    z.steps ≤ localTime + ∑ k, queries k * price k

theorem SourceBudget.local_bound (P : Primitives base Op) (contract : ReplyContract base Cmd)
    (kind : {a b : Ty Atom} → Cmd a b → K) {Γ a} (code : Program Op Cmd Γ a)
    (env : Env base Γ) (localTime : Nat) (queries : K → Nat)
    (h : SourceBudget P contract kind code env localTime queries)
    (z : Run (a.Value base))
    (hz : z ∈ support (code.run P (pricedRequests contract (fun _ => 0)) env)) :
    z.steps ≤ localTime := by
  simpa using h (fun _ => 0) z hz

variable {I S : Type} {target : OracleSpec I}

theorem pricedRequests_dominates (contract : ReplyContract base Cmd)
    (implementation : HandlerM base Cmd (StateT S (OracleComp target)))
    (fee : {a b : Ty Atom} → Cmd a b → Nat) (inv : S → Prop) (potential : S → Int)
    (hstep : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base) s, inv s →
      ∀ z ∈ support ((implementation cmd arg).run s),
        inv z.2 ∧ contract.allows cmd arg z.1.value ∧
          (z.1.steps : Int) + potential z.2 ≤ (fee cmd : Int) + potential s)
    {a b} (cmd : Cmd a b) (arg : a.Value base) :
    DominatedBy inv potential (implementation cmd arg) (pricedRequests contract fee cmd arg) := by
  intro s hs z hz
  obtain ⟨hs', ha, hc⟩ := hstep cmd arg s hs z hz
  refine ⟨hs', ⟨z.1.value, fee cmd⟩, ?_, rfl, hc⟩
  simp only [pricedRequests, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  exact ⟨⟨z.1.value, ha⟩, mem_support_query _ _, rfl⟩

/-- Amortized substitution with an integer potential. Negative potentials track accumulated
storage work; positive potentials bound state growth. No sign condition is assumed. -/
theorem SourceBudget.potential_bound (P : Primitives base Op)
    (contract : ReplyContract base Cmd) (kind : {a b : Ty Atom} → Cmd a b → K)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) (localTime : Nat) (queries : K → Nat)
    (hsource : SourceBudget P contract kind code env localTime queries)
    (implementation : HandlerM base Cmd (StateT S (OracleComp target)))
    (price : K → Nat) (inv : S → Prop) (potential : S → Int)
    (hstep : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base) s, inv s →
      ∀ z ∈ support ((implementation cmd arg).run s),
        inv z.2 ∧ contract.allows cmd arg z.1.value ∧
          (z.1.steps : Int) + potential z.2 ≤ (price (kind cmd) : Int) + potential s)
    (s : S) (hs : inv s) (z : Run (a.Value base) × S)
    (hz : z ∈ support ((code.run P implementation env).run s)) :
    inv z.2 ∧ (z.1.steps : Int) + potential z.2 ≤
      (localTime + ∑ k, queries k * price k : Nat) + potential s := by
  obtain ⟨hs', r, hr, _, hc⟩ := code.run_dominated P inv potential implementation
    (pricedRequests contract (fun cmd => price (kind cmd)))
    (pricedRequests_dominates contract implementation _ inv potential hstep) env s hs z hz
  have hb := hsource price r hr
  have hb' : (r.steps : Int) ≤ (localTime + ∑ k, queries k * price k : Nat) := by exact_mod_cast hb
  exact ⟨hs', by omega⟩

/-- Concrete substitution bound, including the adversary's local computation. Handler work
can include sampling, cache traversal, transcript updates, and algebraic computation. Their
bounds must be proved for the actual implemented handlers under the state invariant. -/
theorem SourceBudget.implemented_bound (P : Primitives base Op)
    (contract : ReplyContract base Cmd) (kind : {a b : Ty Atom} → Cmd a b → K)
    {Γ a} (code : Program Op Cmd Γ a) (env : Env base Γ) (localTime : Nat) (queries : K → Nat)
    (hsource : SourceBudget P contract kind code env localTime queries)
    (implementation : HandlerM base Cmd (StateT S (OracleComp target)))
    (price : K → Nat) (inv : S → Prop)
    (hstep : ∀ {a b} (cmd : Cmd a b) (arg : a.Value base) s, inv s →
      ∀ z ∈ support ((implementation cmd arg).run s),
        inv z.2 ∧ contract.allows cmd arg z.1.value ∧ z.1.steps ≤ price (kind cmd))
    (s : S) (hs : inv s) (z : Run (a.Value base) × S)
    (hz : z ∈ support ((code.run P implementation env).run s)) :
    inv z.2 ∧ z.1.steps ≤ localTime + ∑ k, queries k * price k := by
  have h := SourceBudget.potential_bound P contract kind code env localTime queries hsource implementation
    price inv (fun _ => 0) (by
      intro a b cmd arg s hs z hz
      obtain ⟨hi, ha, hc⟩ := hstep cmd arg s hs z hz
      exact ⟨hi, ha, by simpa using (show (z.1.steps : Int) ≤ price (kind cmd) by exact_mod_cast hc)⟩)
    s hs z hz
  refine ⟨h.1, ?_⟩
  have hi : (z.1.steps : Int) ≤ (localTime + ∑ k, queries k * price k : Nat) := by simpa using h.2
  exact_mod_cast hi

end Signatures.Runtime
