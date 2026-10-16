import Signatures.Schnorr.Game
import Signatures.Model.CyclicCurveNonzeroSampling
import Signatures.Schnorr.GeneralROMSecurityModel
import Signatures.Schnorr.GeneralNonzeroROMParameters

/-! Inspectable execution contracts, nonzero-nonce EUF-CMA game and DLog supremum
for the general Schnorr ROM statement. No algebraic interface is imposed. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr.ListROM

namespace Schnorr.NonzeroNonce

universe v w x

/-- Original backend, encoding, sampling and primitive contracts, fixed before
the attacker is chosen. These fields contain no completed solver budget or
cryptographic hardness assumption. Group sampling follows from the curve's
scalar sampler and generator bijection. -/
class ROMSecurityModel (curve : Model.CyclicCurve) extends Schnorr.ROMExecutionModel.{v, w} curve where
  parameters : ∀ n, QueryAllowance → GeneralROM.Parameters.{v, w, x}
    (Q := quantitative) (F := curve.Scalar n) (G := curve.Group n) (M := Message n)
  queries_eq : ∀ n q, (parameters n q).queries = q
  generator_eq : ∀ n q, (parameters n q).generator = curve.generator n

variable (curve : Model.CyclicCurve) [model : ROMSecurityModel.{v, w, x} curve]

/-- Any general implementation within its declared execution, stored-code and
query allowances. The source is the adaptive nonzero-nonce Schnorr adversary;
no algebraicity, arithmetic-language certificate or fixed query schedule is required. -/
abbrev UnrestrictedAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  GeneralROM.UnrestrictedAdversary (model.parameters securityParameter queries)

/-- Derived cost of setup, both attacker executions, lazy hashing/signing,
private-tape replay, selection, extraction and uniform fallback. -/
noncomputable def romReductionTime (securityParameter : Nat) (queries : QueryAllowance) : Nat :=
  (model.parameters securityParameter queries).solverTime

/-- Nonzero-nonce Schnorr EUF-CMA: generate `pk = x • g`, give the attacker
adaptive randomness/hash/signing access, then verify `z • g = R + H(m,R) • pk`
and require the message to be unsigned. Signing samples uniformly from nonzero
scalars. All hash/signing/final-verification calls share the same initially empty lazy oracle. The model's generator equals the
curve's generator by `ROMSecurityModel.generator_eq`. -/
noncomputable def romEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) : ProbComp Bool :=
  Schnorr.Game.nonzeroRom curve securityParameter adversary.source.main

/-- Supremum of DLog success in the same fixed backend: sample `x`, run the
solver on `(g, x • g)`, and test its answer against `x`. Every challenge fits
the encoded input cap; full stored code/advice meets the derived code allowance,
and runtime is bounded on every supported execution. An optimal solver need
not exist. A hardness assumption makes this quantity small.

`GeneralROM.reduction_within` derives the actual reduction's membership from
original component contracts and the attacker's own resources. -/
noncomputable def romDLogSuccessBound (securityParameter : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : NativeSolver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.inputWidth resources.solverCode time solver),
    𝒟[DiffieHellman.dlogExperiment resources.generator solver] {true}

end Schnorr.NonzeroNonce
