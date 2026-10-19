import Signatures.Runtime.Caliper.BLSCallerPresentation
import Lean.Util.CollectAxioms

/-! A stateless caller may select different queries. Its source is constructed
from its transitions; pending zero-fuel and endlessly adaptive callers are
excluded by the termination premise, rather than silently converted to returns. -/
namespace SignaturesTest.CaliperCallerPresentation
open OracleComp OracleSpec Signatures.Runtime.CaliperBackend
open PFunctor.DynSystem.DynComputation

private def spec : OracleSpec Bool := fun _ => Bool
private def reply (_ : Bool) (answer : Bool) : Bool := answer
private def advance (value : Unit × Bool) : Bool ⊕ (Bool × Unit) := .inl value.2
private def initial (query : Bool) : Bool ⊕ (Bool × Unit) := .inr (query, ())
private def machine := CallerMachine.ofCaller (spec := spec) id reply advance initial

-- Both queries share exactly the same private state; the packet retains which
-- query to make. This was not expressible by a state view of Unit alone.
example : machine.view (machine.init false) ≠ machine.view (machine.init true) := by
  intro equal
  simp only [machine, CallerMachine.ofCaller, ofStep_init, initial, view_ofStep, Sum.inr.injEq] at equal
  have positions := congrArg Sigma.fst equal
  cases positions

example (q : Bool) : CallerMachine.Matches machine id Sum.inr (initial q) (machine.init q) :=
  CallerMachine.ofCaller_matches _ _ _ _ _

private theorem terminates (q : Bool) :
    CallerMachine.Terminates (spec := spec) id reply advance 1 (initial q) := by
  simp [CallerMachine.Terminates, initial, advance]

example (q : Bool) : ¬ CallerMachine.Terminates (spec := spec) id reply advance 0 (initial q) := by
  simp [CallerMachine.Terminates, initial]

private noncomputable def source := CallerMachine.sourceOfCaller (spec := spec) id reply advance initial 1 terminates

-- The chosen finite tree is the original one-query program, not a fallback
-- result or an assumption about a completed reduction.
private theorem source_eq (q : Bool) : source q = spec.query q := by
  have implemented := CallerMachine.ofCaller_implements (spec := spec) id reply advance initial 1 terminates q
  change some <$> (spec.query q : OracleComp spec Bool) = some <$> source q at implemented
  have cancel : ∀ first second : OracleComp spec Bool,
      some <$> first = some <$> second → first = second := by
    intro first second equal
    have observed := congrArg (fun program : OracleComp spec (Option Bool) =>
      (fun result => result.getD false) <$> program) equal
    simpa using observed
  exact cancel _ _ implemented.symm

private def continueWithReply (value : Unit × Bool) : Bool ⊕ (Bool × Unit) := .inr (value.2, ())
private theorem repeat_never_terminates (fuel : Nat) (q : Bool) :
    ¬ CallerMachine.Terminates (spec := spec) id reply continueWithReply fuel (initial q) := by
  induction fuel generalizing q with
  | zero => simp [CallerMachine.Terminates, initial]
  | succ fuel ih =>
      intro terminates
      exact ih false (terminates false)

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``CallerMachine.ofCaller_matches, ``CallerMachine.ofCaller_advance,
      ``CallerMachine.terminates_iff_resolvesIn, ``CallerMachine.ofCaller_implements,
      ``BLSFull.Caller.representReply_eq, ``BLSFull.Caller.Correspondence.ofCaller,
      ``source_eq, ``repeat_never_terminates] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  let type := (← getConstInfo ``BLSFull.Caller.Correspondence.ofCaller).type
  for forbidden in #[``OracleMachine, ``ImplementsWithin, ``OracleComp] do
    if (type.find? (fun expression => expression.isConstOf forbidden)).isSome then
      throwError "caller constructor assumes a separate machine/source certificate: {forbidden}"
  unless (type.find? (fun expression => expression.isConstOf ``BLSFull.Caller.Terminates)).isSome do
    throwError "caller constructor must require actual branchwise termination"

end SignaturesTest.CaliperCallerPresentation
