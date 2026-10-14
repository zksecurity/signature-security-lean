import Signatures.Runtime.GeneralCallerBudget
import Signatures.Runtime.GeneralCallerRefinement

/-! The costed evaluator follows actual quantitative execution traces.

This bridge lets separate backend-work, query-count, and representation-size
bounds supply the symbolic-price caller certificate. Traces record every enabled
reply update; terminal readout and initialization are charged separately.
-/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open QuantitativeRealization

namespace Signatures.Runtime.GeneralCaller

variable {I A B : Type} {spec : OracleSpec I}
  {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq I] {Q : QuantitativeStepClass C}
  {bd : Boundary C spec.toPFunctor A B}
  {R : Caller (Q := Q) (bd := bd)}

def traceFees (fee : I → Nat) {start finish : R.machine.State} :
    R.ExecutionTrace start finish → Nat
  | .nil _ => 0
  | .query (position := i) _ _ tail => fee i + traceFees fee tail

def readResult (R : Caller (Q := Q) (bd := bd)) (state : R.machine.State) : Option B :=
  match R.machine.view state with
  | .inl result => some result
  | .inr _ => none

theorem runFrom_trace (contract : ReplyContract spec) (fee : I → Nat)
    (fuel : Nat) (state : R.machine.State) (z : Run (Option B))
    (hz : z ∈ support (runFrom R (pricedReplies contract fee) fuel state)) :
    ∃ finish, ∃ trace : R.ExecutionTrace state finish,
      trace.Conforms contract.allows ∧ trace.length ≤ fuel ∧
      z.value = readResult R finish ∧
      z.steps = trace.cost.work + Q.cost R.headCode finish +
        traceFees fee trace + 2 * trace.length + 1 := by
  induction fuel generalizing state z with
  | zero =>
      simp only [runFrom, support_pure, Set.mem_singleton_iff] at hz
      subst z
      refine ⟨state, .nil state, trivial, by simp [ExecutionTrace.length], rfl, ?_⟩
      simp [ExecutionTrace.cost, ExecutionTrace.length, traceFees]
  | succ fuel ih =>
      cases hv : R.machine.view state with
      | inl result =>
          simp only [runFrom, hv, support_pure, Set.mem_singleton_iff] at hz
          subst z
          refine ⟨state, .nil state, trivial, by simp [ExecutionTrace.length], ?_, ?_⟩
          · simp [readResult, hv]
          · simp [ExecutionTrace.cost, ExecutionTrace.length, traceFees]
      | inr request =>
          rcases request with ⟨i, next⟩
          simp only [runFrom, hv, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
          obtain ⟨answer, ha, rest, hr, rfl⟩ := hz
          simp only [pricedReplies, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at ha
          obtain ⟨reply, _, rfl⟩ := ha
          obtain ⟨finish, trace, hconf, hlen, hvalue, hsteps⟩ := ih (next reply.val) rest hr
          refine ⟨finish, .query hv reply.val trace, ⟨reply.property, hconf⟩,
            by simpa [ExecutionTrace.length] using Nat.succ_le_succ hlen, hvalue, ?_⟩
          dsimp
          simp only [ExecutionTrace.cost, ExecutionCost.work_add, ExecutionCost.work_ofWork,
            ExecutionCost.work_observe, ExecutionCost.work_query, ExecutionTrace.length, traceFees]
          omega

theorem run_trace (contract : ReplyContract spec) (fee : I → Nat)
    (fuel : Nat) (input : A) (z : Run (Option B))
    (hz : z ∈ support (run R (pricedReplies contract fee) fuel input)) :
    ∃ finish, ∃ trace : R.ExecutionTrace (R.machine.init input) finish,
      trace.Conforms contract.allows ∧ trace.length ≤ fuel ∧
      z.value = readResult R finish ∧
      z.steps = (R.executionCost input trace).work + traceFees fee trace + 2 * trace.length + 2 := by
  simp only [run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨rest, hr, rfl⟩ := hz
  obtain ⟨finish, trace, hc, hl, hv, ht⟩ := runFrom_trace contract fee fuel _ rest hr
  refine ⟨finish, trace, hc, hl, hv, ?_⟩
  dsimp
  simp only [executionCost, ExecutionCost.work_add, ExecutionCost.work_ofWork,
    ExecutionCost.work_observe]
  omega

variable {J S : Type} {target : OracleSpec J}

/-- Per-request prices may depend on the encoded request, rather than being
constant for each oracle kind. Their pathwise sum is charged explicitly. -/
theorem implemented_bound_of_trace_fees (contract : ReplyContract spec) (fee : I → Nat)
    (fuel : Nat) (input : A) (budget : Nat)
    (htrace : ∀ finish (trace : R.ExecutionTrace (R.machine.init input) finish),
      trace.Conforms contract.allows → trace.length ≤ fuel →
        (R.executionCost input trace).work + traceFees fee trace + 2 * trace.length + 2 ≤ budget)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (inv : S → Prop)
    (hstep : ∀ i s, inv s → ∀ z ∈ support ((implementation i).run s),
      inv z.2 ∧ contract.allows i z.1.value ∧ z.1.steps ≤ fee i)
    (s : S) (hs : inv s) (z : Run (Option B) × S)
    (hz : z ∈ support ((run R implementation fuel input).run s)) :
    inv z.2 ∧ z.1.steps ≤ budget := by
  have hdom := pricedReplies_dominates contract implementation fee inv (fun _ => 0) (by
    intro i s hs z hz
    obtain ⟨hi, ha, hc⟩ := hstep i s hs z hz
    exact ⟨hi, ha, by exact_mod_cast hc⟩)
  obtain ⟨hi, reference, hr, _, hcost⟩ := run_dominated R inv (fun _ => 0)
    implementation (pricedReplies contract fee) hdom fuel input s hs z hz
  obtain ⟨finish, trace, hc, hl, _, ht⟩ := run_trace contract fee fuel input reference hr
  have hb : reference.steps ≤ budget := by rw [ht]; exact htrace finish trace hc hl
  refine ⟨hi, ?_⟩
  have hc' : (z.1.steps : Int) ≤ reference.steps := by simpa using hcost
  have hc : z.1.steps ≤ reference.steps := by exact_mod_cast hc'
  exact hc.trans hb

/-- Any execution through conforming stateful handlers follows a syntactic
caller trace. Removing costs here is proof instrumentation, not execution. -/
theorem implemented_trace (contract : ReplyContract spec)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (inv : S → Prop)
    (hstep : ∀ i s, inv s → ∀ z ∈ support ((implementation i).run s),
      inv z.2 ∧ contract.allows i z.1.value)
    (fuel : Nat) (input : A) (s : S) (hs : inv s) (z : Run (Option B) × S)
    (hz : z ∈ support ((run R implementation fuel input).run s)) :
    inv z.2 ∧ ∃ finish, ∃ trace : R.ExecutionTrace (R.machine.init input) finish,
      trace.Conforms contract.allows ∧ trace.length ≤ fuel ∧ z.1.value = readResult R finish := by
  have he := congrArg (fun p => p.run s) (zeroHandler_erase R implementation fuel input)
  simp only [StateT.run_map] at he
  have hm : (z.1.value, z.2) ∈ support
      ((fun p : Run (Option B) × S => (p.1.value, p.2)) <$>
        ((run R (zeroHandler implementation) fuel input).run s)) := by
    rw [he, support_map]
    exact ⟨z, hz, rfl⟩
  rw [support_map] at hm
  obtain ⟨⟨r, state⟩, hr, hv⟩ := hm
  have hstate : state = z.2 := congrArg Prod.snd hv
  subst state
  have hvalue : r.value = z.1.value := congrArg Prod.fst hv
  have hdom := pricedReplies_dominates contract (zeroHandler implementation)
    (fun _ => 0) inv (fun _ => 0) (by
      intro i state hi out hout
      simp only [zeroHandler, StateT.run_map, support_map, Set.mem_image] at hout
      obtain ⟨p, hp, rfl⟩ := hout
      obtain ⟨hn, ha⟩ := hstep i state hi p hp
      exact ⟨hn, ha, by simp⟩)
  obtain ⟨hi, reference, href, hval, _⟩ := run_dominated R inv (fun _ => 0)
    (zeroHandler implementation) (pricedReplies contract (fun _ => 0)) hdom
    fuel input s hs (r, z.2) hr
  obtain ⟨finish, trace, hc, hl, ht, _⟩ := run_trace contract _ fuel input reference href
  exact ⟨hi, finish, trace, hc, hl, hvalue.symm.trans (hval.symm.trans ht)⟩

/-- Representation-size bounds on the caller's reachable readouts transfer to
the actual simulator execution, using an explicit payload-decoding size law. -/
theorem implemented_output_size (contract : ReplyContract spec)
    (implementation : Handler (spec := spec) (StateT S (OracleComp target)))
    (inv : S → Prop)
    (hstep : ∀ i s, inv s → ∀ z ∈ support ((implementation i).run s),
      inv z.2 ∧ contract.allows i z.1.value)
    (recovery : OutputSizeRecovery (Q := Q) (bd := bd))
    (fuel : Nat) (input : A) (headSize : Nat)
    (hsize : ∀ finish (trace : R.ExecutionTrace (R.machine.init input) finish),
      trace.Conforms contract.allows → trace.length ≤ fuel →
        (R.executionCost input trace).peakHeadSize ≤ headSize)
    (s : S) (hs : inv s) (z : Run (Option B) × S)
    (hz : z ∈ support ((run R implementation fuel input).run s))
    (output : B) (hout : z.1.value = some output) :
    Q.size bd.out output ≤ recovery.recover headSize := by
  obtain ⟨_, finish, trace, hc, hl, hv⟩ :=
    implemented_trace contract implementation inv hstep fuel input s hs z hz
  have hread : readResult R finish = some output := hv.symm.trans hout
  have hview : R.machine.view finish = .inl output := by
    cases he : R.machine.view finish with
    | inl value =>
        have hv : value = output := by simpa [readResult, he] using hread
        simp [hv]
    | inr request => simp [readResult, he] at hread
  exact (R.returnedSize_le_peakHeadSize recovery input trace output hview).trans
    (recovery.monotone (hsize finish trace hc hl))

variable {K : Type} [Fintype K] [DecidableEq K]

theorem traceFees_eq_sum (kind : I → K) (price : K → Nat)
    {start finish : R.machine.State} (trace : R.ExecutionTrace start finish) :
    traceFees (fun i => price (kind i)) trace = ∑ k, trace.queryCount kind k * price k := by
  induction trace with
  | nil => simp [traceFees, ExecutionTrace.queryCount]
  | @query state i next finish hv reply tail ih =>
      have hstep : ∀ k, (if kind i = k then tail.queryCount kind k + 1
          else tail.queryCount kind k) * price k =
          tail.queryCount kind k * price k + if kind i = k then price k else 0 := by
        intro k
        split <;> simp_all [Nat.add_mul]
      simp only [traceFees, ExecutionTrace.queryCount, hstep, Finset.sum_add_distrib, ih]
      simp [Nat.add_comm]

/-- Backend work and per-kind query bounds on every admitted execution prefix
derive the evaluator's symbolic-price budget. No reduction budget is assumed. -/
theorem budget_of_trace_bounds (contract : ReplyContract spec) (kind : I → K)
    (fuel : Nat) (input : A) (localTime : Nat) (queries : K → Nat)
    (htrace : ∀ finish (trace : R.ExecutionTrace (R.machine.init input) finish),
      trace.Conforms contract.allows → trace.length ≤ fuel →
        (R.executionCost input trace).work + 2 * trace.length + 2 ≤ localTime ∧
          ∀ k, trace.queryCount kind k ≤ queries k) :
    Budget R contract kind fuel input localTime queries := by
  intro price z hz
  obtain ⟨finish, trace, hc, hl, _, ht⟩ := run_trace contract _ fuel input z hz
  obtain ⟨hlocal, hqueries⟩ := htrace finish trace hc hl
  rw [ht, traceFees_eq_sum]
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ => Nat.mul_le_mul_right (price k) (hqueries k))
  omega

/-- An upstream quantitative execution bound supplies a caller budget directly.
The local allowance adds exactly the evaluator's dispatch/return charges. The
total query cap is conservative for each kind; tighter per-kind caps can use
`budget_of_trace_bounds` instead. -/
theorem budget_of_runsWithinUnder (contract : ReplyContract spec) (kind : I → K)
    (bound : A → ExecutionCost) (hrun : R.RunsWithinUnder contract.allows bound)
    (fuel : Nat) (input : A) :
    Budget R contract kind fuel input
      ((bound input).work + 2 * (bound input).queries + 2)
      (fun _ => (bound input).queries) := by
  apply budget_of_trace_bounds contract kind fuel input _ _
  intro finish trace hc _
  have hw := (hrun.cost_le input trace hc).1
  have hl := hrun.traceLength_le input trace hc
  exact ⟨by omega, fun k => hrun.queryCount_le kind k input trace hc⟩

end Signatures.Runtime.GeneralCaller
