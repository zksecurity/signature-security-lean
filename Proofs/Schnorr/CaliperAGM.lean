import Signatures.Schnorr.CaliperAGMParameters

/-! The public Schnorr Caliper resource witness is constructed from the fixed
components and the attacker's local implementation. No complete-solver bound
or source-reduction implementation is an input certificate. -/
namespace Schnorr.CaliperAGM
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
variable {F G M : Type} [Field F] [SampleableType F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] [DecidableEq M]
    {queries : QueryAllowance} {generator : G}
    (P : Parameters F G M queries generator) (A : AlgebraicAdversary P)

theorem reduction_within : P.within P.solverTime (Signatures.Runtime.SchnorrAGM.dlogReduction A.source) :=
  CaliperBackend.SchnorrAGM.Full.dlogWithin P.layout P.routines P.scalarSource P.scalarLaw
    A.caller P.primitiveBounds P.callerLimits A.bounds P.sampler queries.total P.samplerTime P.samplerWords
    P.samplerNames P.samplerFits P.addresses P.samplerCorrect A.invariant A.correspondence A.source A.source_eq
    ⟨generator, P.generatorValid⟩

theorem security [Fintype F] (generates : Function.Injective (fun scalar : F => scalar • generator)) :
    𝒟[AGM.game generator A.source] {true} ≤ P.dlogBound P.solverTime +
      (queries.hash + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * (Fintype.card F : ENNReal)⁻¹ :=
  CaliperBackend.SchnorrAGM.Full.security P.layout P.routines P.scalarSource P.scalarLaw
    A.caller P.primitiveBounds P.callerLimits A.bounds P.sampler queries.total P.samplerTime P.samplerWords
    P.samplerNames P.samplerFits P.addresses P.samplerCorrect A.invariant A.correspondence A.source A.source_eq
    ⟨generator, P.generatorValid⟩ generates A.signingQueries A.hashQueries

end Schnorr.CaliperAGM
