import Signatures.Schnorr.CaliperAGMParameters
import Proofs.Runtime.Caliper.SchnorrAGMCallerPresentation

/-! Build the public Schnorr attacker certificate from local Caliper code and
branchwise query allowances. Its capacity invariant, source machine and source
query bounds are derived. The algebraic source and its identification with the
derived tree remain explicit; no conventional-machine coverage is claimed. -/
namespace Schnorr.CaliperAGM
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
open Signatures.Runtime.SchnorrAGM.Native
variable {F G M : Type} [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M]
    {queries : QueryAllowance} {generator : G}
    (P : Parameters F G M queries generator)
    (caller : CaliperBackend.SchnorrAGM.Full.Caller P.layout)

/-- All reply branches terminate within total fuel and respect each query kind. -/
structure CallerQueries : Prop where
  random : CaliperBackend.SchnorrAGM.Full.Caller.QueryBound P.layout P.routines.handler.zeroValid caller
    (fun q => randomRequest q = true) queries.random queries.total
  hash : CaliperBackend.SchnorrAGM.Full.Caller.QueryBound P.layout P.routines.handler.zeroValid caller
    (fun q => AGM.Reduction.hashRequest q = true) queries.hash queries.total
  sign : CaliperBackend.SchnorrAGM.Full.Caller.QueryBound P.layout P.routines.handler.zeroValid caller
    (fun q => AGM.Reduction.signRequest q = true) queries.sign queries.total

variable (allowances : CallerQueries P caller)
def CallerQueries.invariant : CaliperBackend.SchnorrAGM.Full.Caller.Invariant P.layout caller queries.total :=
  CaliperBackend.SchnorrAGM.Full.Caller.Invariant.ofQueryBounds P.layout P.routines.handler.zeroValid caller
    allowances.hash allowances.sign

omit [DecidableEq F] [DecidableEq G] [DecidableEq M] in
include allowances in
theorem CallerQueries.terminates :
    CaliperBackend.SchnorrAGM.Full.Caller.Terminates P.layout P.routines.handler.zeroValid caller queries.total :=
  CaliperBackend.SchnorrAGM.Full.Caller.QueryBound.toTerminates _ _ _ _ _ allowances.random

noncomputable def Parameters.callerCorrespondence :
    CaliperBackend.SchnorrAGM.Full.Caller.Source P.layout caller queries.total (allowances.invariant P caller) :=
  CaliperBackend.SchnorrAGM.Full.Caller.Source.ofCaller P.layout P.routines.handler.zeroValid caller
    (allowances.invariant P caller) (allowances.terminates P caller)

variable (generates : Function.Surjective (fun scalar : F => scalar • generator))

omit [DecidableEq F] [DecidableEq G] [DecidableEq M] in
include generates in
theorem Parameters.point_valid (point : G) : P.layout.service.scheme.point.valid point := by
  obtain ⟨scalar, rfl⟩ := generates point
  exact (CaliperBackend.SchnorrAGM.Full.challenge_valid P.layout P.routines P.scalarSource P.scalarLaw
    ⟨generator, P.generatorValid⟩ scalar).2

/-- The source retains the shared AGM algebraicity contract. Everything about
its local machine presentation and resource/query certificates is constructed. -/
noncomputable def AlgebraicAdversary.ofCaller
    (resources : CaliperBackend.SchnorrAGM.Full.Caller.Bounds P.layout caller P.callerLimits)
    (source : AGM.Adversary F G M)
    (same : ∀ value, (fun answer => Interface.decodeForgery answer.val) <$>
      (P.callerCorrespondence caller allowances).program value =
        source.main (AGM.initial value.val.1 value.val.2)) : AlgebraicAdversary P :=
  { source := source
    caller := caller
    invariant := allowances.invariant P caller
    correspondence := P.callerCorrespondence caller allowances
    source_eq := same
    bounds := resources
    randomQueries := by
      intro pk
      rw [← same ⟨(generator, pk), P.generatorValid, P.point_valid generates pk⟩]
      apply (isQueryBoundP_map_iff _ _ queries.random).mpr
      exact CaliperBackend.SchnorrAGM.Full.Caller.Source.ofCaller_queryBound _ _ _ _ _ _ _
        allowances.random _
    hashQueries := by
      intro pk
      rw [← same ⟨(generator, pk), P.generatorValid, P.point_valid generates pk⟩]
      apply (isQueryBoundP_map_iff _ _ queries.hash).mpr
      exact CaliperBackend.SchnorrAGM.Full.Caller.Source.ofCaller_queryBound _ _ _ _ _ _ _
        allowances.hash _
    signingQueries := by
      intro pk
      rw [← same ⟨(generator, pk), P.generatorValid, P.point_valid generates pk⟩]
      apply (isQueryBoundP_map_iff _ _ queries.sign).mpr
      exact CaliperBackend.SchnorrAGM.Full.Caller.Source.ofCaller_queryBound _ _ _ _ _ _ _
        allowances.sign _ }

end Schnorr.CaliperAGM
