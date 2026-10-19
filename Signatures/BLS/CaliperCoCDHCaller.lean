import Signatures.BLS.CaliperCoCDHParameters
import Signatures.Runtime.Caliper.CoronCallerPresentation

/-! Construct a public ordinary attacker from local Caliper code and its local
resource/query allowances. Source, termination, invariant, machine presentation
and source query bounds are derived. The finite source tree is a mathematical
description; the executable remains the existing local caller and controller. -/
namespace BLS.CaliperCoCDH
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
variable {F G K M : Type} [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [AddCommGroup K] [Module F K] [DecidableEq M]
    {queries : QueryAllowance} {generator : G} {keyGenerator : K}
    (P : Parameters F G K M queries generator keyGenerator)
    (generates : Function.Surjective (fun scalar : F => scalar • generator))

omit [DecidableEq M] in
include generates in
theorem Parameters.point_valid (point : G) : P.service.point.valid point :=
  CoronFull.point_valid P.service P.sampler P.routines ⟨generator, P.generatorValid⟩ generates point

variable (caller : CoronCaller.Caller P.layout)
noncomputable def Parameters.callerCorrespondence
    (terminates : CoronCaller.Caller.Terminates P.key P.layout (P.point_valid generates) caller queries.total) :
    CoronCaller.Caller.Correspondence P.layout caller
      (CoronCaller.Caller.Invariant.ofTerminates P.key P.layout (P.point_valid generates) caller terminates) K :=
  CoronCaller.Caller.Correspondence.ofCaller P.key P.layout (P.point_valid generates) caller terminates
    ⟨keyGenerator, P.keyGeneratorValid⟩

/-- Each path of local transitions obeys the three allowances and ends before
the total query fuel is exhausted. These conditions do not mention a source tree. -/
structure CallerQueries : Prop where
  random : CoronCaller.Caller.QueryBound P.key P.layout (P.point_valid generates) caller
    (fun i => queryKind i = 0) queries.random queries.total
  hash : CoronCaller.Caller.QueryBound P.key P.layout (P.point_valid generates) caller
    (fun i => queryKind i = 1) queries.hash queries.total
  sign : CoronCaller.Caller.QueryBound P.key P.layout (P.point_valid generates) caller
    (fun i => Sum.isRight i = true) queries.sign queries.total

omit [DecidableEq M] in
theorem CallerQueries.terminates (bounded : CallerQueries P generates caller) :
    CoronCaller.Caller.Terminates P.key P.layout (P.point_valid generates) caller queries.total :=
  CoronCaller.Caller.QueryBound.toTerminates _ _ _ _ _ _ bounded.random

/-- An ordinary public attacker assembled entirely from its implemented local
steps, their resource bounds and branchwise query allowances. -/
noncomputable def Adversary.ofCaller
    (resources : CoronCaller.Caller.Fits P.layout caller P.callerLimits)
    (allowances : CallerQueries P generates caller) : Adversary P :=
  let terminates := allowances.terminates P generates caller
  let witness := P.callerCorrespondence generates caller terminates
  { source := fun pk => (Subtype.val <$> witness.source pk : OracleComp (ROM.advSpec M G) (M × G))
    caller := caller
    invariant := CoronCaller.Caller.Invariant.ofTerminates P.key P.layout (P.point_valid generates) caller terminates
    correspondence := witness
    inputView := fun _ => rfl
    source_eq := fun _ => rfl
    localTime := resources.stepTime
    initialTime := resources.initialTime
    localWords := resources.stepWords
    initialWords := resources.initialWords
    localNames := resources.stepNames
    initialNames := resources.initialNames
    randomQueries := fun pk => (isQueryBoundP_map_iff _ Subtype.val queries.random).mpr
      (CoronCaller.Caller.Correspondence.ofCaller_queryBound P.key P.layout (P.point_valid generates) caller terminates
        ⟨keyGenerator, P.keyGeneratorValid⟩ (fun i => queryKind i = 0) queries.random allowances.random pk)
    hashQueries := fun pk => (isQueryBoundP_map_iff _ Subtype.val queries.hash).mpr
      (CoronCaller.Caller.Correspondence.ofCaller_queryBound P.key P.layout (P.point_valid generates) caller terminates
        ⟨keyGenerator, P.keyGeneratorValid⟩ (fun i => queryKind i = 1) queries.hash allowances.hash pk)
    signingQueries := fun pk => (isQueryBoundP_map_iff _ Subtype.val queries.sign).mpr
      (CoronCaller.Caller.Correspondence.ofCaller_queryBound P.key P.layout (P.point_valid generates) caller terminates
        ⟨keyGenerator, P.keyGeneratorValid⟩ (fun i => Sum.isRight i = true) queries.sign allowances.sign pk) }

end BLS.CaliperCoCDH
