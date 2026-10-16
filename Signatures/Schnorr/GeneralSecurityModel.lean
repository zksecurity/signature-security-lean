import Signatures.Schnorr.Game
import Signatures.Model.CyclicCurve
import Signatures.Schnorr.GeneralAGMParameters

/-! Inspectable execution contracts, EUF-CMA game and resource-indexed DLog
success bound for the public Schnorr AGM theorem. The mathematical curve has a
single group. The execution model is fixed before choosing the attacker. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native

namespace Schnorr

universe v w x

/-- General local computation with measured costs and sizes. Messages need
decidable equality, with no finite-domain requirement. Request equality is used
by the dependent interaction interface; executed comparisons are priced separately. -/
class ExecutionModel (curve : Model.CyclicCurve) where
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
  [requestEquality : ∀ n, DecidableEq (Interface.SourceRequest (curve.Scalar n) (curve.Group n) (Message n))]

attribute [instance_reducible, instance] ExecutionModel.products ExecutionModel.sums ExecutionModel.options
  ExecutionModel.category ExecutionModel.quantitativeProducts ExecutionModel.quantitativeSums
  ExecutionModel.quantitativeOptions ExecutionModel.distributive ExecutionModel.optionCode
  ExecutionModel.messageEquality ExecutionModel.requestEquality

/-- Component implementations, resource allowances and their local contracts.
The detailed fields are in `GeneralAGMParameters.lean`. This record supplies
neither a completed-reduction runtime bound nor a cryptographic hardness assumption. -/
class AGMSecurityModel (curve : Model.CyclicCurve) extends ExecutionModel.{v, w} curve where
  parameters : ∀ n, QueryAllowance → GeneralAGM.Parameters.{v, w, x}
    (Q := quantitative) (F := curve.Scalar n) (G := curve.Group n) (M := Message n)
  queries_eq : ∀ n q, (parameters n q).queries = q
  generator_eq : ∀ n q, (parameters n q).generator = curve.generator n

variable (curve : Model.CyclicCurve) [model : AGMSecurityModel.{v, w, x} curve]

/-- Any implemented algebraic attacker within the model's own execution,
code/advice and query allowances. Its local code need not use our arithmetic
language. Group requests and the final commitment carry valid representations
in the chronological group inputs received on that path. -/
abbrev AlgebraicAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  GeneralAGM.AlgebraicAdversary (model.parameters securityParameter queries)

/-- The proved complete native solver time: setup, attacker execution, lazy
oracle simulation, conversions, extraction and cutoff handling are included. -/
def agmReductionTime (securityParameter : Nat) (queries : QueryAllowance) : Nat :=
  (model.parameters securityParameter queries).solverTime

/-- The full-field-nonce Schnorr EUF-CMA game. A signature is `(R,z)` with
`z • g = R + H(m,R) • pk`. Hashing, signing and final verification share a lazy
oracle. Signing records messages; malformed requests permanently prevent a win.
The source handler samples a fresh nonce and returns its commitment on signing. -/
noncomputable def agmEufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) : ProbComp Bool :=
  Schnorr.Game.agm curve securityParameter adversary.source

/-- Supremum of DLog success in the same fixed backend: draw uniform x, give
the solver `(g, x • g)`, and test whether it returns x. Every challenge fits the
input bound; stored code/data meets the derived code bound and runtime is at
most `time` on every supported execution. No optimal solver need exist.

The time/code formulas are `GeneralAGM.Parameters.solverTime` and `solverCode`;
`GeneralAGM.reduction_within` proves that the constructed reduction satisfies them.
A DLog hardness assumption is needed to make this quantity small. -/
noncomputable def dlogSuccessBound (securityParameter : Nat) (queries : QueryAllowance)
    (time : Nat) : ENNReal :=
  let resources := model.parameters securityParameter queries
  ⨆ solver, ⨆ (_ : Solver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.inputWidth resources.solverCode time solver),
    𝒟[DiffieHellman.dlogExperiment resources.generator solver] {true}

end Schnorr
