import Signatures.Model.PairingCurve
import Signatures.BLS.GeneralAGMStatement

/-! Supporting definitions for the English-shaped BLS security statement.
The public curve contains only mathematical data. This separate model fixes
the backend, message types, and resource limits before an adversary is chosen.
Its contracts are the existing primitive/encoding contracts, not a hypothesis
that the finished reduction is efficient. -/

open OracleComp PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram

namespace BLS

universe v w x

abbrev QueryAllowance := GeneralAGM.QueryAllowance

/-- The declared execution model and attacker resource class for a curve.
Allowances supplied to the public theorem are exactly the allowances enforced
by the underlying attacker certificate, not ignored display arguments. -/
class SecurityModel (curve : Model.PairingCurve) where
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
  parameters : ∀ n, QueryAllowance → GeneralAGM.Parameters.{v, w, x}
    (Q := quantitative) (F := curve.Scalar n) (G₁ := curve.SignatureGroup n)
    (G₂ := curve.KeyGroup n) (Gₜ := curve.TargetGroup n) (M := Message n)
  queries_eq : ∀ n q, (parameters n q).queries = q
  generator_eq : ∀ n q, (parameters n q).generator = curve.generator n
  keyGenerator_eq : ∀ n q, (parameters n q).keyGenerator = curve.keyGenerator n

attribute [instance_reducible, instance] SecurityModel.products SecurityModel.sums SecurityModel.options
  SecurityModel.category SecurityModel.quantitativeProducts SecurityModel.quantitativeSums
  SecurityModel.quantitativeOptions SecurityModel.distributive SecurityModel.optionCode
  SecurityModel.messageEquality

variable (curve : Model.PairingCurve) [model : SecurityModel.{v, w, x} curve]

/-- Any algebraic attacker realized in the declared model, with its own measured
execution/code bounds and the stated random/hash/sign query allowances. -/
abbrev AlgebraicAdversary (securityParameter : Nat) (queries : QueryAllowance) :=
  GeneralAGM.AlgebraicAdversary (model.parameters securityParameter queries)

/-- Each allowance in the public statement bounds that kind of query in the
actual source adversary, at every verification key. -/
theorem AlgebraicAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => GeneralAGM.queryKind i = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => GeneralAGM.queryKind i = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => GeneralAGM.queryKind i = 2) queries.sign) := by
  simpa only [SecurityModel.queries_eq] using
    And.intro adversary.randomQueries (And.intro adversary.hashQueries adversary.signingQueries)

/-- The original BLS lazy-ROM EUF-CMA game, using the supplied curve and attacker. -/
noncomputable def eufCmaGame (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) : ProbComp Bool :=
  BLS.LazyAGM.game (Gₜ := curve.TargetGroup securityParameter)
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source

/-- DLog advantage at the complete good-branch reduction budget in the declared model. -/
noncomputable def goodDLogBound (securityParameter : Nat) (queries : QueryAllowance) : ENNReal :=
  let parameters := model.parameters securityParameter queries
  parameters.dlogBound parameters.goodTime

/-- DLog advantage at the complete bad-branch reduction budget in the same model. -/
noncomputable def badDLogBound (securityParameter : Nat) (queries : QueryAllowance) : ENNReal :=
  let parameters := model.parameters securityParameter queries
  parameters.dlogBound parameters.badTime

end BLS
