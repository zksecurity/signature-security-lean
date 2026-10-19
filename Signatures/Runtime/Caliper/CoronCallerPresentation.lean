import Signatures.Runtime.Caliper.CoronCallerSource
import Signatures.Runtime.Caliper.BLSCallerPresentationBase
import Signatures.Runtime.Caliper.CallerQueryBounds

/-! Construct a co-CDH caller's invariant, source tree and oracle machine from
its local transitions. No separate source or completed reduction is supplied.
Unrepresented keys use a source-only extension; all executed inputs are kept. -/
namespace Signatures.Runtime.CaliperBackend.CoronCaller.Caller
open Caliper BoundedSource OracleComp OracleSpec
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G K A : Type}
    {service : CoronService.Layouts w M F G randomBound qS} (key : Layout w K)
    (layout : Layouts service A key.Value) (pointValid : ∀ point, service.point.valid point)
    (caller : Caller layout)

abbrev representReply := BLSCallerHandler.representReply service.service randomBound pointValid
def Terminates (fuel : Nat) : Prop := ∀ input,
  CallerMachine.Terminates (BLSCallerHandler.query service.service randomBound)
    (representReply pointValid) caller.advance fuel (caller.initial input)

variable {fuel : Nat} (terminates : Terminates key layout pointValid caller fuel)
def Invariant.ofTerminates : Invariant layout caller fuel where
  domain := BLSCallerHandler.terminationDomain service.service randomBound pointValid caller.advance
  advance := BLSCallerHandler.termination_advance service.service randomBound pointValid caller.advance
  initial input := (BLSCallerHandler.headValid_iff_terminates service.service randomBound pointValid caller.advance
    fuel (caller.initial input)).mpr (terminates input)

variable (fallback : key.Value)
noncomputable def initialOnKeys : K → layout.Next := CallerMachine.extendInput key.valid fallback caller.initial
theorem initialOnKeys_valid (input : key.Value) :
    initialOnKeys key layout caller fallback input.val = caller.initial input :=
  CallerMachine.extendInput_valid _ _ _ input
include terminates in
theorem initialOnKeys_terminates (input : K) :
    CallerMachine.Terminates (BLSCallerHandler.query service.service randomBound)
      (representReply pointValid) caller.advance fuel (initialOnKeys key layout caller fallback input) :=
  CallerMachine.extendInput_property _ _ _ _ terminates input

noncomputable def Correspondence.ofCaller : Correspondence layout caller
    (Invariant.ofTerminates key layout pointValid caller terminates) K where
  machine := CallerMachine.ofCaller (BLSCallerHandler.query service.service randomBound)
    (representReply pointValid) caller.advance (initialOnKeys key layout caller fallback)
  stateView := Sum.inr
  inputView := Subtype.val
  source := CallerMachine.sourceOfCaller (BLSCallerHandler.query service.service randomBound)
    (representReply pointValid) caller.advance (initialOnKeys key layout caller fallback) fuel
      (initialOnKeys_terminates key layout pointValid caller terminates fallback)
  implements := CallerMachine.ofCaller_implements _ _ _ _ _
    (initialOnKeys_terminates key layout pointValid caller terminates fallback)
  advance := fun _ q c _ next view represented original related =>
    CallerMachine.ofCaller_advance _ _ _ _ q c next view represented original
      (BLSCallerHandler.representReply_eq service.service randomBound pointValid q represented original related)
  initial := by
    intro value
    change CallerMachine.Matches
      (CallerMachine.ofCaller (spec := Model.LazyAGM.advSpec M M G)
        (BLSCallerHandler.query service.service randomBound) (representReply pointValid)
        caller.advance (initialOnKeys key layout caller fallback))
      (BLSCallerHandler.query service.service randomBound) Sum.inr
      (caller.initial value) (initialOnKeys key layout caller fallback value.val)
    rw [initialOnKeys_valid]
    exact CallerMachine.ofCaller_matches _ _ _ _ (caller.initial value)

theorem Correspondence.ofCaller_run (input : key.Value) :
    (Correspondence.ofCaller key layout pointValid caller terminates fallback).machine.unroll fuel (caller.initial input) =
      some <$> (Correspondence.ofCaller key layout pointValid caller terminates fallback).source input.val := by
  have implemented := (Correspondence.ofCaller key layout pointValid caller terminates fallback).implements input.val
  change (Correspondence.ofCaller key layout pointValid caller terminates fallback).machine.unroll fuel
    (initialOnKeys key layout caller fallback input.val) = _ at implemented
  rw [initialOnKeys_valid] at implemented
  exact implemented

variable (predicate : (Model.LazyAGM.advSpec M M G).Domain → Prop) [DecidablePred predicate]
    (count : Nat)
def QueryBound (fuel : Nat) : Prop := ∀ input,
  CallerMachine.QueryBound (BLSCallerHandler.query service.service randomBound)
    (representReply pointValid) caller.advance predicate fuel count (caller.initial input)

omit terminates fallback in
theorem QueryBound.toTerminates (bounded : QueryBound key layout pointValid caller predicate count fuel) :
    Terminates key layout pointValid caller fuel :=
  fun input => CallerMachine.QueryBound.terminates _ _ _ _ (bounded input)

theorem Correspondence.ofCaller_queryBound
    (bounded : QueryBound key layout pointValid caller predicate count fuel) (input : K) :
    IsQueryBoundP ((Correspondence.ofCaller key layout pointValid caller terminates fallback).source input) predicate count :=
  CallerMachine.sourceOfCaller_queryBound _ _ _ predicate _ fuel
    (initialOnKeys_terminates key layout pointValid caller terminates fallback) count
    (CallerMachine.extendInput_property _ _ _ _ bounded) input

end Signatures.Runtime.CaliperBackend.CoronCaller.Caller
