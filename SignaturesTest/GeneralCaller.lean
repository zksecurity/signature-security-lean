import Signatures.Runtime.GeneralCoronCorrectness
import Signatures.Runtime.GeneralCallerTrace
import Signatures.Runtime.GeneralCallerOutput
import Signatures.Runtime.GeneralCallerResources
import Lean.Util.CollectAxioms

open OracleComp OracleSpec PFunctor Signatures.Runtime
open PFunctor.DynSystem.DynComputation

namespace SignaturesTest.GeneralCaller

variable {I A B : Type} {spec : OracleSpec I}
  {C : StepClass} [C.HasProd] [C.HasSum] [C.HasOption]
  [DecidableEq I] {Q : QuantitativeStepClass C}
  {bd : Boundary C spec.toPFunctor A B}
  (R : GeneralCaller.Caller (Q := Q) (bd := bd))

-- Even a caller making no queries pays for initialization and terminal readout.
example (H : GeneralCaller.Handler (spec := spec) Id) (input : A) (result : B)
    (hv : R.machine.view (R.machine.init input) = .inl result) :
    (GeneralCaller.run R H 0 input).steps =
      Q.cost R.initCode input + Q.cost R.headCode (R.machine.init input) + 2 := by
  simp [GeneralCaller.run, GeneralCaller.runFrom, Pure.pure, Bind.bind, hv]
  omega

-- A reply-dependent continuation pays for its backend update and its final head.
-- The theorem is uniform in the backend; it does not invent zero-cost realizers.
example (H : GeneralCaller.Handler (spec := spec) Id) (input : A)
    (i : I) (next : spec.Range i → R.machine.State) (answer : spec.Range i)
    (result : B) (handlerSteps : Nat)
    (hv : R.machine.view (R.machine.init input) = .inr ⟨i, next⟩)
    (ha : H i = ⟨answer, handlerSteps⟩)
    (hf : R.machine.view (next answer) = .inl result) :
    GeneralCaller.run R H 1 input =
      ⟨some result, Q.cost R.initCode input + Q.cost R.headCode (R.machine.init input) +
        handlerSteps + Q.cost R.updateCode (R.machine.init input, ⟨i, answer⟩) +
        Q.cost R.headCode (next answer) + 4⟩ := by
  simp [GeneralCaller.run, GeneralCaller.runFrom, Pure.pure, Bind.bind, hv, ha, hf]
  congr 1
  omega

-- Insufficient fuel remains visible, so a cutoff cannot masquerade as a forgery.
example (H : GeneralCaller.Handler (spec := spec) Id) (input : A)
    (i : I) (next : spec.Range i → R.machine.State)
    (hv : R.machine.view (R.machine.init input) = .inr ⟨i, next⟩) :
    (GeneralCaller.run R H 0 input).value = none := by
  simp [GeneralCaller.run, GeneralCaller.runFrom, Pure.pure, Bind.bind, hv]

end SignaturesTest.GeneralCaller

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``GeneralCaller.run_erase, ``GeneralCaller.run_dominated,
      ``GeneralCaller.Budget.implemented_bound, ``GeneralCaller.Budget.potential_bound,
      ``GeneralCaller.run_refines, ``GeneralCaller.run_countCalls_refines,
      ``GeneralCaller.simulateQ_refines,
      ``GeneralCaller.run_trace, ``GeneralCaller.budget_of_trace_bounds,
      ``GeneralCaller.budget_of_runsWithinUnder,
      ``GeneralCaller.implemented_bound_of_trace_fees,
      ``GeneralCaller.implemented_trace, ``GeneralCaller.implemented_output_size,
      ``GeneralCaller.runFrom_output_invariant, ``GeneralCaller.run_output_invariant,
      ``GeneralCaller.reachable_init, ``GeneralCaller.reachable_step,
      ``GeneralCaller.reachable_sizes, ``GeneralCaller.implementsWithin_of_resources,
      ``GeneralCaller.budget_of_resources,
      ``GeneralCaller.Budget.state_growth, ``GeneralCaller.Budget.linear_state_bound,
      ``Coron.generalSimulation_bound, ``Coron.generalReduction_bound,
      ``Coron.generalSimulation_erase, ``Coron.generalReduction_erase_native,
      ``Coron.generalReduction_erase_original, ``Coron.generalSolverRun_erase,
      ``Coron.generalSolverRun_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
