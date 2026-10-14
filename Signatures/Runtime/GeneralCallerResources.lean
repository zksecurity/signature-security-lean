import Signatures.Runtime.GeneralCallerTrace

/-! Derive caller invariants and bounded source implementation from a general
quantitative execution contract. Reachability uses actual typed execution traces,
so closure covers every reply-dependent continuation without a caller-specific
invariant premise. Local code is arbitrary code of the fixed backend. -/

open OracleComp OracleSpec PFunctor
open PFunctor.DynSystem.DynComputation
open QuantitativeRealization

namespace Signatures.Runtime.GeneralCaller

variable {I A B : Type} {spec : OracleSpec I}
  {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq I] {Q : QuantitativeStepClass C}
  {bd : Boundary C spec.toPFunctor A B}
  (R : Caller (Q := Q) (bd := bd))

def Reachable (state : R.machine.State) : Prop :=
  ∃ input, Nonempty (R.ExecutionTrace (R.machine.init input) state)

theorem reachable_init (input : A) : Reachable R (R.machine.init input) :=
  ⟨input, ⟨.nil _⟩⟩

theorem reachable_step (state : R.machine.State) (hs : Reachable R state)
    (i : I) (next : spec.Range i → R.machine.State) (hv : R.machine.view state = .inr ⟨i, next⟩)
    (reply : spec.Range i) : Reachable R (next reply) := by
  obtain ⟨input, ⟨trace⟩⟩ := hs
  exact ⟨input, ⟨trace.append (.query hv reply (.nil _))⟩⟩

theorem reachable_sizes (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (state : R.machine.State) (hs : Reachable R state) :
    Q.size R.state state ≤ bound.peakStateSize ∧
      Q.size bd.head (R.machine.head state) ≤ bound.peakHeadSize := by
  obtain ⟨input, ⟨trace⟩⟩ := hs
  have hc := hrun.cost_le input trace
  refine ⟨?_, (R.finalHeadSize_le_peakHeadSize input trace).trans hc.2.2.2.2⟩
  have hfinal : Q.size R.state state ≤ (R.executionCost input trace).peakStateSize := by
    simp only [executionCost, ExecutionCost.peakStateSize_add, ExecutionCost.peakStateSize_observe]
    omega
  exact hfinal.trans hc.2.2.2.1

theorem implementsWithin_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (program : A → OracleComp spec B) (hprogram : R.machine.Implements program)
    (fuel : Nat) (hfuel : bound.queries ≤ fuel) : R.machine.ImplementsWithin program fuel := by
  rw [implementsWithin_iff_implements_and_resolvesIn]
  exact ⟨hprogram, fun input => (hrun.resolvesIn input).mono hfuel⟩

variable {K : Type} [Fintype K] [DecidableEq K]

/-- Uniform resource bounds give a conservative per-kind budget. Every query
kind may instead use a tighter trace-count bound through `budget_of_trace_bounds`.
The added local allowance is evaluator administration, not reduction work. -/
theorem budget_of_resources (bound : ExecutionCost) (hrun : R.RunsWithin (fun _ => bound))
    (contract : ReplyContract spec)
    (kind : I → K) (fuel : Nat) (input : A) :
    Budget R contract kind fuel input (bound.work + 2 * bound.queries + 2) (fun _ => bound.queries) := by
  apply budget_of_trace_bounds contract kind fuel input _ _
  intro finish trace _ _
  have hw := (hrun.cost_le input trace).1
  have hl := hrun.traceLength_le input trace
  exact ⟨by omega, fun k => hrun.queryCount_le kind k input trace⟩

end Signatures.Runtime.GeneralCaller
