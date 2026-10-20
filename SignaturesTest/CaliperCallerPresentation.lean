import Signatures.BLS.CaliperAGMParameters
import Signatures.Runtime.Caliper.CallerQueryBounds
import Signatures.Schnorr.CaliperAGMCaller
import Lean.Util.CollectAxioms

/-! A stateless caller may select different queries. Its source is constructed
from its transitions; pending zero-fuel and endlessly adaptive callers are
excluded by the termination premise, rather than silently converted to returns. -/
namespace SignaturesTest.CaliperCallerPresentation
open OracleComp OracleSpec Signatures.Runtime.CaliperBackend
open PFunctor.DynSystem.DynComputation

-- A finite represented subset of an infinite key type is enough. Extension
-- preserves every admitted input and uses its represented fallback elsewhere.
example (key : {value : Nat // value < 4}) :
    CallerMachine.extendInput (fun value : Nat => value < 4) ⟨1, by decide⟩ Subtype.val key.val = key.val :=
  CallerMachine.extendInput_valid _ _ _ key

example : CallerMachine.extendInput (fun value : Nat => value < 4)
    ⟨1, by decide⟩ Subtype.val 1000 = 1 := by
  simp [CallerMachine.extendInput]

example (key : Nat) : CallerMachine.extendInput (fun value : Nat => value < 4)
    ⟨1, by decide⟩ Subtype.val key < 4 :=
  CallerMachine.extendInput_property _ _ _ (fun value => value < 4) Subtype.property key

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

-- Counted queries and total termination are separate checks. An uncounted
-- request still requires fuel; an exhausted count cannot hide a counted call.
example : CallerMachine.QueryBound (spec := spec) id reply advance (fun q => q = true) 1 0 (initial false) := by
  simp [CallerMachine.QueryBound, initial, advance]
example : ¬ CallerMachine.QueryBound (spec := spec) id reply advance (fun q => q = true) 1 0 (initial true) := by
  simp [CallerMachine.QueryBound, initial]
example : ¬ CallerMachine.QueryBound (spec := spec) id reply advance (fun q => q = true) 0 0 (initial false) := by
  simp [CallerMachine.QueryBound, initial]

-- The first answer selects the second query. Every branch must respect the
-- allowance, including the branch that makes a counted query.
private def adaptive (value : Bool × Bool) : Bool ⊕ (Bool × Bool) :=
  if value.1 then .inl value.2 else .inr (value.2, true)
private def adaptiveInitial (_ : Unit) : Bool ⊕ (Bool × Bool) := .inr (false, false)
private theorem adaptive_bound (input : Unit) :
    CallerMachine.QueryBound (spec := spec) id reply adaptive (fun q => q = true) 2 1 (adaptiveInitial input) := by
  refine ⟨Or.inr (by decide), ?_⟩
  intro answer
  exact ⟨Or.inr (by decide), fun _ => trivial⟩
private theorem adaptive_over_budget :
    ¬ CallerMachine.QueryBound (spec := spec) id reply adaptive (fun q => q = true) 2 0 (adaptiveInitial ()) := by
  intro bounded
  rcases (bounded.2 true).1 with forbidden | positive
  · exact forbidden rfl
  · exact Nat.not_lt_zero _ positive
private theorem adaptive_terminates (input : Unit) :
    CallerMachine.Terminates (spec := spec) id reply adaptive 2 (adaptiveInitial input) :=
  CallerMachine.QueryBound.terminates _ _ _ _ (adaptive_bound input)
private noncomputable def adaptiveSource :=
  CallerMachine.sourceOfCaller (spec := spec) id reply adaptive adaptiveInitial 2 adaptive_terminates
private theorem adaptive_source_bound (input : Unit) :
    IsQueryBoundP (adaptiveSource input) (fun q => q = true) 1 :=
  CallerMachine.sourceOfCaller_queryBound _ _ _ _ _ _ adaptive_terminates 1 adaptive_bound input

open Lean Meta in
run_meta do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``CallerMachine.ofCaller_matches, ``CallerMachine.ofCaller_advance,
      ``CallerMachine.extendInput_valid, ``CallerMachine.extendInput_property,
      ``CallerMachine.terminates_iff_resolvesIn, ``CallerMachine.ofCaller_implements,
      ``BLSFull.Caller.representReply_eq, ``BLSFull.Caller.Correspondence.ofCaller,
      ``BLSFull.point_valid, ``BLS.CaliperAGM.Parameters.point_valid,
      ``BLS.CaliperAGM.Parameters.callerCorrespondence,
      ``CallerMachine.QueryBound.terminates, ``CallerMachine.QueryBound.unroll,
      ``CallerMachine.sourceOfCaller_queryBound,
      ``Synchronizes.mono_left_support,
      ``SchnorrAGM.CallerHandler.source_canonical, ``SchnorrAGM.CallerHandler.canonical_reply_injective,
      ``SchnorrAGM.CallerHandler.representReply_eq, ``SchnorrAGM.Full.Caller.Source.ofCaller,
      ``SchnorrAGM.Full.Caller.Source.ofCaller_run, ``SchnorrAGM.Full.Caller.Source.ofCaller_queryBound,
      ``SchnorrAGM.Full.Caller.Invariant.ofQueryBounds,
      ``Schnorr.CaliperAGM.Parameters.point_valid, ``Schnorr.CaliperAGM.AlgebraicAdversary.ofCaller,
      ``source_eq, ``repeat_never_terminates, ``adaptive_bound, ``adaptive_over_budget,
      ``adaptive_source_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"
  let type := (← getConstInfo ``BLSFull.Caller.Correspondence.ofCaller).type
  for forbidden in #[``OracleMachine, ``ImplementsWithin, ``OracleComp] do
    if (type.find? (fun expression => expression.isConstOf forbidden)).isSome then
      throwError "caller constructor assumes a separate machine/source certificate: {forbidden}"
  unless (type.find? (fun expression => expression.isConstOf ``BLSFull.Caller.Terminates)).isSome do
    throwError "caller constructor must require actual branchwise termination"
  let constructor := (← getConstInfo ``BLS.CaliperAGM.Parameters.callerCorrespondence).value?.get!
  for required in #[``BLS.CaliperAGM.Parameters.point_valid, ``BLS.CaliperAGM.Parameters.keyGeneratorValid,
      ``BLSFull.Caller.Correspondence.ofCaller] do
    unless (constructor.find? (fun expression => expression.isConstOf required)).isSome do
      throwError "parameter constructor must derive its representation facts from {required}"

open Lean Meta in
run_meta do
  let constructor := (← getConstInfo ``SchnorrAGM.Full.Caller.Source.ofCaller).type
  for forbidden in #[``OracleMachine, ``ImplementsWithin, ``OracleComp] do
    if (constructor.find? (fun expression => expression.isConstOf forbidden)).isSome then
      throwError "Schnorr caller constructor assumes a separate machine/source certificate: {forbidden}"
  unless (constructor.find? (fun expression => expression.isConstOf ``SchnorrAGM.Full.Caller.Terminates)).isSome do
    throwError "Schnorr caller construction must require branchwise termination"
  forallTelescope (← getConstInfo ``Schnorr.CaliperAGM.AlgebraicAdversary.ofCaller).type fun params _ => do
    for param in params do
      let premise ← inferType param
      for forbidden in #[``OracleMachine, ``SchnorrAGM.Full.Caller.Source, ``SchnorrAGM.Full.Caller.Invariant,
          ``Interactive.Within, ``cyclicDLogWithin] do
        if (premise.find? (fun expression => expression.isConstOf forbidden)).isSome then
          throwError "Schnorr public constructor requires a derived certificate: {forbidden}"
  let publicConstructor := (← getConstInfo ``Schnorr.CaliperAGM.AlgebraicAdversary.ofCaller).value?.get!
  for required in #[``Schnorr.CaliperAGM.CallerQueries.invariant,
      ``Schnorr.CaliperAGM.Parameters.callerCorrespondence] do
    unless (publicConstructor.find? (fun expression => expression.isConstOf required)).isSome do
      throwError "Schnorr public caller constructor omits derived obligation {required}"
  let presentation := (← getConstInfo ``Schnorr.CaliperAGM.Parameters.callerCorrespondence).value?.get!
  unless (presentation.find? (fun expression => expression.isConstOf ``SchnorrAGM.Full.Caller.Source.ofCaller)).isSome do
    throwError "Schnorr correspondence must construct the local machine and source"

section SchnorrConstructor
open Caliper OracleSpec Signatures.Runtime BoundedSource
variable {F G M : Type} [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M]
    {queries : Schnorr.QueryAllowance} {generator : G}
    (P : Schnorr.CaliperAGM.Parameters F G M queries generator)
    (caller : SchnorrAGM.Full.Caller P.layout)
    (allowances : Schnorr.CaliperAGM.CallerQueries P caller)
    (generates : Function.Surjective (fun scalar : F => scalar • generator))
    (resources : SchnorrAGM.Full.Caller.Bounds P.layout caller P.callerLimits)
    (source : Schnorr.AGM.Adversary F G M)
    (same : ∀ value, (fun answer => SchnorrAGM.Native.Interface.decodeForgery answer.val) <$>
      (P.callerCorrespondence caller allowances).program value =
        source.main (Schnorr.AGM.initial value.val.1 value.val.2))

example : (Schnorr.CaliperAGM.AlgebraicAdversary.ofCaller P caller allowances generates resources source same).source = source := rfl
example : SchnorrAGM.Full.Caller.Invariant P.layout caller queries.total := allowances.invariant P caller
end SchnorrConstructor

end SignaturesTest.CaliperCallerPresentation
