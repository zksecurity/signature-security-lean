import Signatures.Schnorr.CaliperROMParameters
import Signatures.Runtime.Caliper.SchnorrROMNonzeroFullSecurity

/-! The nonzero-nonce attacker over the same fixed Caliper components. Only the
signing branch's source law differs: it simulates the nonzero-nonce list
backend (`Parameters.Nonzero`). -/
namespace Schnorr.CaliperROM
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
variable {F G M : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    {queries : QueryAllowance} {generator : G} (P : Parameters F G M queries generator)

/-- The signing branch simulates the nonzero-nonce scheme's list backend, with
the ambient nonzero-scalar sampler. -/
def Parameters.Nonzero [SampleableType Fˣ] : Prop :=
  letI := SchnorrROMTape.PrivateSampler.Enumerated.sampleable P.config.sampler
  P.law.target = Schnorr.NonzeroListROM.handler (G₂ := G) (K := M)

/-- Arbitrary local Caliper code over the fixed caller shape attacking the
nonzero-nonce scheme, with its own resource and query allowances and a source
correspondence for its machine. -/
structure NonzeroAdversary [SampleableType F] [SampleableType Fˣ] [SampleableType G] where
  source : NonzeroNonce.Adversary (F := F) (M := M) generator
  caller : SchnorrROM.Full.Caller P.config P.shape
  bounds : caller.Bounds P.config P.shape P.limits
  correspondence : SchnorrROM.Pass.Caller.Source P.config (caller.toPass P.config P.shape) queries.total
  source_eq : ∀ pk : P.config.point.Value,
    Subtype.val <$> correspondence.program (correspondence.inputView pk) = source.main pk.val
  randomQueries : ∀ pk, IsQueryBoundP (source.main pk) (· matches .inl (.inl _)) queries.random
  signingQueries : ∀ pk, IsQueryBoundP (source.main pk) (· matches .inr _) queries.sign
  hashQueries : ∀ pk, IsQueryBoundP (source.main pk) (· matches .inl (.inr _)) queries.hash

variable [inst : SampleableType F] [SampleableType Fˣ] [SampleableType G] (A : NonzeroAdversary P)
    (sampled : inst = SchnorrROMTape.PrivateSampler.Enumerated.sampleable P.config.sampler) (nonzero : P.Nonzero)

include sampled nonzero in
theorem nonzero_reduction_within :
    P.within P.solverTime (Schnorr.NonzeroListROM.NativeSolver.reduction (G₂ := G) (K := M) A.source.main queries.hash) :=
  SchnorrROM.Full.Nonzero.dlogWithin P.config P.shape A.caller P.operations P.law nonzero P.handlerBudget queries.hash P.indexFits
    P.limits A.bounds P.arithmetic P.arithmeticBudget P.handlerRoom P.slotsRoom queries.total P.tables P.tapes sampled
    A.correspondence A.source.main A.source_eq ⟨generator, P.generatorValid⟩

include sampled nonzero in
theorem nonzero_security [Fintype F] (generates : Function.Bijective (fun scalar : F => scalar • generator)) :
    𝒟[NonzeroNonce.game generator A.source] {true} ≤
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ +
      (queries.hash + 1 : ENNReal) * (Fintype.card F : ENNReal)⁻¹ +
      ((queries.hash + 1 : ENNReal) * P.dlogBound P.solverTime) ^ (1 / 2 : ℝ) :=
  SchnorrROM.Full.Nonzero.security P.config P.shape A.caller P.operations P.law nonzero P.handlerBudget queries.hash P.indexFits
    P.limits A.bounds P.arithmetic P.arithmeticBudget P.handlerRoom P.slotsRoom queries.total P.tables P.tapes sampled
    A.correspondence ⟨generator, P.generatorValid⟩ generates A.source queries.sign A.source_eq
    (fun pk => ⟨A.signingQueries pk, A.hashQueries pk⟩)

end Schnorr.CaliperROM
