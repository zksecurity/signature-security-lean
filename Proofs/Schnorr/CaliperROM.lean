import Signatures.Schnorr.CaliperROMParameters

/-! The public ordinary-ROM Caliper resource witness is constructed from the
fixed components and the attacker's local implementation; the forking bound is
stated in that replaying reduction's DLog success. No complete-solver bound or
source-reduction implementation is an input certificate. -/
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

theorem security [Fintype F] (generates : Function.Bijective (fun scalar : F => scalar • generator)) :
    𝒟[ROM.game generator A.source] {true} ≤
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * (Fintype.card F : ENNReal)⁻¹ +
      (queries.hash + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
      ((queries.hash + 1 : ENNReal) * 𝒟[DiffieHellman.dlogExperiment generator
        (Schnorr.ListROM.NativeSolver.reduction (G₂ := G) (K := M) A.source.main queries.hash)] {true}) ^ (1 / 2 : ℝ) := by
  have fork := Schnorr.LazyROM.security generator generates A.source queries.sign queries.hash
    (fun pk => ⟨A.signingQueries pk, A.hashQueries pk⟩)
  rw [← Schnorr.ListROM.NativeSolver.reduction_experiment (G₂ := G) (K := M)] at fork
  exact Model.forking_inverse queries.hash (MeasureTheory.measure_ne_top _ _)
    (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) fork

end Schnorr.CaliperROM
