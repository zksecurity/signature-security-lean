import VCVio.OracleComp.QueryTracking.QueryBound

/-! Reachable prefixes of an adaptive source computation interpreted by a
stateful oracle. Each transition uses a supported answer and state of that
same handler. This is a proof relation, not executable machine bookkeeping. -/

namespace Signatures.Runtime.CaliperBackend

open OracleComp OracleSpec

variable {I J S A : Type} {spec : OracleSpec I} {target : OracleSpec J}

inductive SourcePrefix (handler : QueryImpl spec (StateT S (OracleComp target)))
    (main : OracleComp spec A) (initial : S) : OracleComp spec A → S → Nat → Prop
  | start : SourcePrefix handler main initial main initial 0
  | step {query : I} {next : spec.Range query → OracleComp spec A} {state : S} {used : Nat}
      (path : SourcePrefix handler main initial (queryBind query next) state used)
      (answer : spec.Range query × S) (supported : answer ∈ support ((handler query).run state)) :
      SourcePrefix handler main initial (next answer.1) answer.2 (used + 1)

namespace SourcePrefix

variable {handler : QueryImpl spec (StateT S (OracleComp target))}
    {main residual : OracleComp spec A} {initial state : S} {used : Nat}

theorem append {middle : OracleComp spec A} {saved : S} {firstUsed secondUsed : Nat}
    (first : SourcePrefix handler main initial middle saved firstUsed)
    (second : SourcePrefix handler middle saved residual state secondUsed) :
    SourcePrefix handler main initial residual state (firstUsed + secondUsed) := by
  induction second with
  | start => exact first
  | step path answer supported ih =>
    simpa only [Nat.add_assoc] using SourcePrefix.step ih answer supported

/-- Every supported result of the original stateful simulation has a complete
path in this relation. Prefix invariants therefore cover its actual runs. -/
theorem complete (result : A × S)
    (supported : result ∈ support ((simulateQ handler main).run initial)) :
    ∃ count, SourcePrefix handler main initial (pure result.1) result.2 count := by
  induction main using OracleComp.inductionOn generalizing initial with
  | pure value =>
    have equal : result = (value, initial) := by simpa using supported
    subst result
    exact ⟨0, .start⟩
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨answer, answered, finished⟩ := supported
    obtain ⟨count, rest⟩ := ih answer.1 finished
    have first : SourcePrefix handler (liftM (spec.query query) >>= next) initial
        (next answer.1) answer.2 1 :=
      .step .start answer answered
    exact ⟨1 + count, first.append rest⟩

theorem queryBound (path : SourcePrefix handler main initial residual state used)
    {budget : Nat} (bounded : IsTotalQueryBound main budget) :
    used ≤ budget ∧ IsTotalQueryBound residual (budget - used) := by
  induction path with
  | start => exact ⟨Nat.zero_le _, bounded⟩
  | @step query next state used path answer supported ih =>
    have limits := isTotalQueryBound_query_bind_iff.mp
      (show IsTotalQueryBound (liftM (spec.query query) >>= next) (budget - used) from ih.2)
    exact ⟨by omega, by simpa only [Nat.sub_add_eq] using limits.2 answer.1⟩

theorem allowed (path : SourcePrefix handler main initial residual state used)
    {predicate : I → Prop} (queries : AllQueriesSatisfy main predicate) :
    AllQueriesSatisfy residual predicate := by
  induction path with
  | start => exact queries
  | step path answer supported ih => exact ih.2 answer.1

theorem growth (path : SourcePrefix handler main initial residual state used)
    (size : S → Nat)
    (stepBound : ∀ query state answer, answer ∈ support ((handler query).run state) →
      size answer.2 ≤ size state + 1) :
    size state ≤ size initial + used := by
  induction path with
  | start => exact Nat.le_refl _
  | step path answer supported ih =>
    have bound := stepBound _ _ answer supported
    omega

end SourcePrefix
end Signatures.Runtime.CaliperBackend
