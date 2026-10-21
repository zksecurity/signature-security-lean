import Signatures.Schnorr.Game
import Signatures.Model.CyclicCurveSampling
import Signatures.Model.CyclicCurveNonzeroSampling
import Signatures.Schnorr.CaliperNonzeroROMParameters

/-! Inspectable game and Caliper resource model for the public nonzero-nonce
Schnorr ROM statement. The components are the full-field route's, with the
signing branch simulating the nonzero-nonce list backend. -/

open OracleComp OracleSpec

namespace Schnorr.NonzeroNonce

/-- Fixed Caliper components, with no completed-reduction certificate. The
curve's scalar sampler is the enumerated draw the handler executes, and the
signing branch simulates nonzero-nonce signing under the curve's nonzero sampler. -/
class ROMSecurityModel (curve : Model.CyclicCurve) where
  Message : Nat → Type
  [messageEquality : ∀ n, DecidableEq (Message n)]
  parameters : ∀ n q, CaliperROM.Parameters (curve.Scalar n) (curve.Group n) (Message n) q (curve.generator n)
  sampling : ∀ n q, curve.scalarSampling n =
    Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.sampleable (parameters n q).config.sampler
  nonzero : ∀ n q, (parameters n q).Nonzero

attribute [instance_reducible, instance] ROMSecurityModel.messageEquality

variable (curve : Model.CyclicCurve) [model : ROMSecurityModel curve]

/-- Any local Caliper implementation over the fixed caller shape, within its
declared execution, stored-code and query allowances. The source is the adaptive
nonzero-nonce Schnorr adversary; no algebraicity, arithmetic-language certificate
or fixed query schedule is required. -/
abbrev UnrestrictedAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  CaliperROM.NonzeroAdversary (model.parameters securityParameter queries)

/-- Derived cost of setup, both attacker executions, lazy hashing/signing,
private-tape replay, selection, extraction and uniform fallback. -/
def romReductionTime (securityParameter : Nat) (queries : QueryAllowance) : Nat :=
  (model.parameters securityParameter queries).solverTime

/-- Nonzero-nonce Schnorr EUF-CMA: generate `pk = x • g`, give the attacker
adaptive randomness/hash/signing access, then verify `z • g = R + H(m,R) • pk`
and require the message to be unsigned. Signing samples uniformly from nonzero
scalars. All hash/signing/final-verification calls share the same initially empty lazy oracle. -/
noncomputable def romEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) : ProbComp Bool :=
  Schnorr.Game.nonzeroRom curve securityParameter adversary.source.main

/-- Supremum of DLog success in the fixed Caliper model at the derived code and
total-memory limits and the displayed runtime limit (see `Schnorr.romDLogSuccessBound`). -/
noncomputable def romDLogSuccessBound (securityParameter : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : Signatures.Runtime.CaliperBackend.cyclicDLogWithin
      (Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh.port resources.config.handler.sampler.tape)
      (Signatures.Runtime.CaliperBackend.SchnorrROM.Pass.Initialization.points resources.config)
      resources.config.handler.sampler.tape.scalar (curve.generator securityParameter)
      resources.solverCode resources.solverMemory time solver),
    𝒟[DiffieHellman.dlogExperiment (curve.generator securityParameter) solver] {true}

end Schnorr.NonzeroNonce
