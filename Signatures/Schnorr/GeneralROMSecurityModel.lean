import Signatures.Schnorr.Game
import Signatures.Model.CyclicCurveSampling
import Signatures.Schnorr.GeneralROMParameters
import Signatures.Schnorr.CaliperROMParameters

/-! Inspectable game and Caliper resource model for the public ordinary-ROM
Schnorr statement. Implemented primitives, layouts, caller shape and allowances
are fixed before choosing the attacker. The game remains independent of this
model. The abstract backend's execution model is retained below for the
nonzero-nonce route. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr.ListROM

namespace Schnorr

universe v w x

/-- The common execution model for arbitrary local attacker computation and
the reduction in the abstract backend. Encoded sizes and operation costs are
measured by this model. Messages require equality, with no finite-domain or
default-message assumption. -/
class ROMExecutionModel (curve : Model.CyclicCurve) where
  steps : StepClass.{0, v}
  [products : steps.HasProd]
  [sums : steps.HasSum]
  [options : steps.HasOption]
  quantitative : QuantitativeStepClass.{0, v, w} steps
  [category : quantitative.HasCategory]
  [quantitativeProducts : quantitative.HasProd]
  [quantitativeSums : quantitative.HasSum]
  [quantitativeOptions : quantitative.HasOption]
  [distributive : quantitative.IsDistributive]
  [optionCode : OptionCode (Q := quantitative)]
  Message : Nat → Type
  [messageEquality : ∀ n, DecidableEq (Message n)]

attribute [instance_reducible, instance] ROMExecutionModel.products ROMExecutionModel.sums ROMExecutionModel.options
  ROMExecutionModel.category ROMExecutionModel.quantitativeProducts ROMExecutionModel.quantitativeSums
  ROMExecutionModel.quantitativeOptions ROMExecutionModel.distributive ROMExecutionModel.optionCode
  ROMExecutionModel.messageEquality

/-- Fixed Caliper components, with no completed-reduction certificate. The
fields are in `CaliperROMParameters.lean`; the actual setup, replaying
controller, extraction and fallback are constructed and proved separately. The
curve's scalar sampler is the enumerated draw that the handler executes. -/
class ROMSecurityModel (curve : Model.CyclicCurve) where
  Message : Nat → Type
  [messageEquality : ∀ n, DecidableEq (Message n)]
  parameters : ∀ n q, CaliperROM.Parameters (curve.Scalar n) (curve.Group n) (Message n) q (curve.generator n)
  sampling : ∀ n q, curve.scalarSampling n =
    Signatures.Runtime.CaliperBackend.SchnorrROMTape.PrivateSampler.Enumerated.sampleable (parameters n q).config.sampler
  fullField : ∀ n q, (parameters n q).FullField

attribute [instance_reducible, instance] ROMSecurityModel.messageEquality

variable (curve : Model.CyclicCurve) [model : ROMSecurityModel curve]

/-- Any local Caliper implementation over the fixed caller shape, within its
declared execution, stored-code and query allowances. The source is the ordinary
adaptive Schnorr adversary; no algebraicity, arithmetic-language certificate or
fixed query schedule is required. -/
abbrev UnrestrictedAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  CaliperROM.UnrestrictedAdversary (model.parameters securityParameter queries)

/-- Derived cost of setup, both attacker executions, lazy hashing/signing,
private-tape replay, selection, extraction and uniform fallback. -/
def romReductionTime (securityParameter : Nat) (queries : QueryAllowance) : Nat :=
  (model.parameters securityParameter queries).solverTime

/-- Full-field-nonce Schnorr EUF-CMA: generate `pk = x • g`, give the attacker
adaptive randomness/hash/signing access, then verify `z • g = R + H(m,R) • pk`
and require the message to be unsigned. All hash/signing/final-verification calls
share the same initially empty lazy oracle. -/
noncomputable def romEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) : ProbComp Bool :=
  Schnorr.Game.rom curve securityParameter adversary.source.main

/-- Supremum of DLog success in the fixed Caliper model: sample `x`, run the
solver on `(g, x • g)`, and test its answer against `x`. Solvers use the fixed
port and layouts with the derived code and total-memory limits and the displayed
runtime limit. Every challenge must be represented. An optimal solver need not
exist. `CaliperROM.reduction_within` constructs the actual reduction witness;
a hardness assumption makes this quantity small. -/
noncomputable def romDLogSuccessBound (securityParameter : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : Signatures.Runtime.CaliperBackend.cyclicDLogWithin
      (Signatures.Runtime.CaliperBackend.SchnorrROMTape.Fresh.port resources.config.handler.sampler.tape)
      (Signatures.Runtime.CaliperBackend.SchnorrROM.Pass.Initialization.points resources.config)
      resources.config.handler.sampler.tape.scalar (curve.generator securityParameter)
      resources.solverCode resources.solverMemory time solver),
    𝒟[DiffieHellman.dlogExperiment (curve.generator securityParameter) solver] {true}

end Schnorr
