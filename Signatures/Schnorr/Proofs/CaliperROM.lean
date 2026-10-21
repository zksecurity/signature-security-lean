import Signatures.Schnorr.CaliperROMParameters

/-! The public ordinary-ROM Caliper resource witness is constructed from the
fixed components and the attacker's local implementation. No complete-solver
bound or source-reduction implementation is an input certificate. -/
namespace Schnorr.CaliperROM
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    {queries : QueryAllowance} {generator : G}
    (P : Parameters F G M queries generator) [inst : SampleableType F] [SampleableType G] (A : UnrestrictedAdversary P)
    (sampled : inst = SchnorrROMTape.PrivateSampler.Enumerated.sampleable P.config.sampler) (full : P.FullField)

include sampled full in
theorem reduction_within :
    P.within P.solverTime (Schnorr.ListROM.NativeSolver.reduction (G₂ := G) (K := M) A.source.main queries.hash) :=
  SchnorrROM.Full.dlogWithin P.config P.shape A.caller P.operations P.law full P.handlerBudget queries.hash P.indexFits P.limits A.bounds
    P.arithmetic P.arithmeticBudget P.handlerRoom P.slotsRoom queries.total P.tables P.tapes sampled A.correspondence
    A.source.main A.source_eq ⟨generator, P.generatorValid⟩

include sampled full in
theorem security [Fintype F] (generates : Function.Bijective (fun scalar : F => scalar • generator)) :
    𝒟[ROM.game generator A.source] {true} ≤
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * (Fintype.card F : ENNReal)⁻¹ +
      (queries.hash + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
      ((queries.hash + 1 : ENNReal) * P.dlogBound P.solverTime) ^ (1 / 2 : ℝ) :=
  SchnorrROM.Full.security P.config P.shape A.caller P.operations P.law full P.handlerBudget queries.hash P.indexFits P.limits A.bounds
    P.arithmetic P.arithmeticBudget P.handlerRoom P.slotsRoom queries.total P.tables P.tapes sampled A.correspondence
    ⟨generator, P.generatorValid⟩ generates A.source queries.sign A.source_eq
    (fun pk => ⟨A.signingQueries pk, A.hashQueries pk⟩)

end Schnorr.CaliperROM
