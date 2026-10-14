import Signatures.Runtime.GeneralCaller

/-! Resource substitution for callers with backend-realized local computation.

The caller certificate quantifies over every admitted reply path and every
nonnegative oracle price. A simulator supplies only per-request certificates;
the completed execution bound is a conclusion. Reply contracts can express
encoded-size bounds, and cannot make a request's response set empty.
-/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation

namespace Signatures.Runtime.GeneralCaller

variable {I A B : Type} {spec : OracleSpec I}
  {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq I] {Q : QuantitativeStepClass C}
  {bd : Boundary C spec.toPFunctor A B}

structure ReplyContract (spec : OracleSpec I) where
  allows : (i : I) → spec.Range i → Prop
  responds : ∀ i, ∃ y, allows i y

def admittedSpec (contract : ReplyContract spec) : OracleSpec I :=
  fun i => {y : spec.Range i // contract.allows i y}

def pricedReplies (contract : ReplyContract spec) (fee : I → Nat) :
    Handler (spec := spec) (OracleComp (admittedSpec contract)) := fun i => do
  let y ← (liftM ((admittedSpec contract).query i) :
    OracleComp (admittedSpec contract) {y : spec.Range i // contract.allows i y})
  pure ⟨y.val, fee i⟩

variable (R : Caller (Q := Q) (bd := bd)) {K : Type} [Fintype K]

/-- A bound on the attacker's own realized computation, with symbolic prices
for calls. This does not assume a budget for any completed reduction. -/
def Budget (contract : ReplyContract spec) (kind : I → K)
    (fuel : Nat) (input : A) (localTime : Nat) (queries : K → Nat) : Prop :=
  ∀ price : K → Nat, ∀ z ∈ support
    (run R (pricedReplies contract (fun i => price (kind i))) fuel input),
      z.steps ≤ localTime + ∑ k, queries k * price k

theorem Budget.local_bound (contract : ReplyContract spec) (kind : I → K)
    (fuel : Nat) (input : A) (localTime : Nat) (queries : K → Nat)
    (h : Budget R contract kind fuel input localTime queries)
    (z : Run (Option B))
    (hz : z ∈ support (run R (pricedReplies contract (fun _ => 0)) fuel input)) :
    z.steps ≤ localTime := by
  simpa using h (fun _ => 0) z hz

variable {J S : Type} {target : OracleSpec J}

omit [DecidableEq I] in
theorem pricedReplies_dominates (contract : ReplyContract spec)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (fee : I → Nat) (inv : S → Prop) (potential : S → Int)
    (hstep : ∀ i s, inv s → ∀ z ∈ support ((implementation i).run s),
      inv z.2 ∧ contract.allows i z.1.value ∧
        (z.1.steps : Int) + potential z.2 ≤ (fee i : Int) + potential s)
    (i : I) :
    DominatedBy inv potential (implementation i) (pricedReplies contract fee i) := by
  intro s hs z hz
  obtain ⟨hs', ha, hc⟩ := hstep i s hs z hz
  refine ⟨hs', ⟨z.1.value, fee i⟩, ?_, rfl, hc⟩
  simp only [pricedReplies, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  exact ⟨⟨z.1.value, ha⟩, mem_support_query _ _, rfl⟩

/-- The handler potential tracks amortized storage work without imposing any
sign convention. Caller local work is preserved exactly. -/
theorem Budget.potential_bound (contract : ReplyContract spec) (kind : I → K)
    (fuel : Nat) (input : A) (localTime : Nat) (queries : K → Nat)
    (hcaller : Budget R contract kind fuel input localTime queries)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (price : K → Nat) (inv : S → Prop) (potential : S → Int)
    (hstep : ∀ i s, inv s → ∀ z ∈ support ((implementation i).run s),
      inv z.2 ∧ contract.allows i z.1.value ∧
        (z.1.steps : Int) + potential z.2 ≤ (price (kind i) : Int) + potential s)
    (s : S) (hs : inv s) (z : Run (Option B) × S)
    (hz : z ∈ support ((run R implementation fuel input).run s)) :
    inv z.2 ∧ (z.1.steps : Int) + potential z.2 ≤
      (localTime + ∑ k, queries k * price k : Nat) + potential s := by
  obtain ⟨hs', r, hr, _, hc⟩ := run_dominated R inv potential implementation
    (pricedReplies contract (fun i => price (kind i)))
    (pricedReplies_dominates contract implementation _ inv potential hstep) fuel input s hs z hz
  have hb := hcaller price r hr
  have hb' : (r.steps : Int) ≤ (localTime + ∑ k, queries k * price k : Nat) := by
    exact_mod_cast hb
  exact ⟨hs', by omega⟩

/-- An actual per-handler cost bound gives a concrete bound for the entire run,
including arbitrary backend-realized attacker computation. -/
theorem Budget.implemented_bound (contract : ReplyContract spec) (kind : I → K)
    (fuel : Nat) (input : A) (localTime : Nat) (queries : K → Nat)
    (hcaller : Budget R contract kind fuel input localTime queries)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (price : K → Nat) (inv : S → Prop)
    (hstep : ∀ i s, inv s → ∀ z ∈ support ((implementation i).run s),
      inv z.2 ∧ contract.allows i z.1.value ∧ z.1.steps ≤ price (kind i))
    (s : S) (hs : inv s) (z : Run (Option B) × S)
    (hz : z ∈ support ((run R implementation fuel input).run s)) :
    inv z.2 ∧ z.1.steps ≤ localTime + ∑ k, queries k * price k := by
  have h := Budget.potential_bound R contract kind fuel input localTime queries hcaller
    implementation price inv (fun _ => 0) (by
      intro i s hs z hz
      obtain ⟨hi, ha, hc⟩ := hstep i s hs z hz
      exact ⟨hi, ha, by exact_mod_cast hc⟩) s hs z hz
  refine ⟨h.1, ?_⟩
  have hi : (z.1.steps : Int) ≤ (localTime + ∑ k, queries k * price k : Nat) := by
    simpa using h.2
  exact_mod_cast hi

end Signatures.Runtime.GeneralCaller
