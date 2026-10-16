import Signatures.BLS.GeneralSecurityModel
import Signatures.BLS.GeneralAGMStatement
import Signatures.BLS.Proofs.ROM

/-! Proofs for the public BLS AGM/DLog and unrestricted co-CDH statements.
First connect the displayed games and allowances to the original source games.
Then combine their probability reductions with constructed native resource
certificates and membership in the explicit hardness suprema. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram

namespace BLS

universe v w x

section AGM

variable (curve : Model.PairingCurve) [model : AGMSecurityModel.{v, w, x} curve]

/-- Each allowance in the public statement bounds that kind of query in the
actual source adversary, at every verification key. -/
theorem AlgebraicAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => GeneralAGM.queryKind i = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => GeneralAGM.queryKind i = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => GeneralAGM.queryKind i = 2) queries.sign) := by
  simpa only [AGMSecurityModel.queries_eq] using
    And.intro adversary.randomQueries (And.intro adversary.hashQueries adversary.signingQueries)

/-- Expanding the public game preserves the exact original game, not just its probability. -/
theorem agmEufCmaGame_eq (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    agmEufCmaGame curve securityParameter adversary =
      LazyAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source := by
  classical
  simp [agmEufCmaGame, Game.agm, LazyAGM.game, Model.LazyAGM.game, Model.LazyAGM.experiment,
    LazyAGM.terms, Model.LazyAGM.evalTerms]
  apply bind_congr
  intro keyAndCache
  apply bind_congr
  intro resultAndCache
  congr 2
  split <;> split <;> simp_all
  grind only

/-- Every algebraic attacker within the declared resources and query allowances obeys
this EUF-CMA bound. `goodTime` and `badTime` are the complete derived reduction times.
The good branch extracts from a nonzero denominator. The bad branch uses independent
affine masks to handle the zero-denominator case; the proof's remaining loss is `1/|F|`. -/
theorem Proofs.agm_security
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    let resources := model.parameters securityParameter queries
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      dlogSuccessBound curve securityParameter queries resources.goodTime +
      dlogSuccessBound curve securityParameter queries resources.badTime +
      1 / (curve.order securityParameter : ENNReal) := by
  let resources := model.parameters securityParameter queries
  -- Probability: the two explicit lazy reductions account for every successful forgery,
  -- apart from the original inverse-field-size loss. This step has no efficiency premise.
  have probabilityBound := LazyAGM.Reduction.security_arbitrary_messages_list
    resources.generator resources.keyGenerator adversary.source resources.generates resources.pairingInjective
  -- Efficiency: construct both native executable witnesses and prove their full budgets.
  obtain ⟨goodFits, badFits⟩ := GeneralAGM.reductions_within resources adversary
  -- Each constructed solver is therefore a member of the supremum above.
  have goodBound : Model.dlog11Advantage resources.generator resources.keyGenerator
      (LazyAGM.Reduction.goodReductionList adversary.source) ≤
      dlogSuccessBound curve securityParameter queries resources.goodTime :=
    le_iSup_of_le _ (le_iSup_of_le goodFits le_rfl)
  have badBound : Model.dlog11Advantage resources.generator resources.keyGenerator
      (LazyAGM.Reduction.badReductionList adversary.source) ≤
      dlogSuccessBound curve securityParameter queries resources.badTime :=
    le_iSup_of_le _ (le_iSup_of_le badFits le_rfl)
  simpa only [resources, agmEufCmaGame_eq, AGMSecurityModel.generator_eq, AGMSecurityModel.keyGenerator_eq,
    Model.PairingCurve.order] using
    probabilityBound.trans (add_le_add (add_le_add goodBound badBound) le_rfl)

/-- Increasing only the time allowance enlarges the same fixed-backend solver
class. Its input and stored-code bounds are unchanged. -/
theorem dlogSuccessBound_mono (securityParameter : Nat) (queries : QueryAllowance) :
    Monotone (dlogSuccessBound curve securityParameter queries) := by
  intro time largerTime ht
  let resources := model.parameters securityParameter queries
  refine iSup_le fun solver => iSup_le fun fits => ?_
  have largerFits : Signatures.Runtime.LazyAGM.NativeSolver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.keyGenerator resources.inputWidth resources.solverCode largerTime solver :=
    ⟨fits.1, Within.mono resources.backend resources.descriptionSizes resources.factor resources.description
      fits.2 le_rfl ht⟩
  exact le_iSup_of_le solver (le_iSup_of_le largerFits le_rfl)

/-- Both DLog solvers fit the maximum of their derived runtimes, yielding one
hardness quantity with a factor of two. The separate-budget theorem is sharper. -/
theorem Proofs.agm_security_common_budget
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      2 * dlogSuccessBound curve securityParameter queries
        (agmReductionTime curve securityParameter queries) +
      1 / (curve.order securityParameter : ENNReal) := by
  let resources := model.parameters securityParameter queries
  have goodBound := dlogSuccessBound_mono curve securityParameter queries
    (Nat.le_max_left resources.goodTime resources.badTime)
  have badBound := dlogSuccessBound_mono curve securityParameter queries
    (Nat.le_max_right resources.goodTime resources.badTime)
  have bound := (Proofs.agm_security curve securityParameter queries adversary).trans
    (add_le_add (add_le_add goodBound badBound) le_rfl)
  simpa only [two_mul, agmReductionTime, resources] using bound

end AGM

section CoCDH

variable (curve : Model.PairingCurve) [model : CoCDHSecurityModel.{v, w, x} curve]

/-- The three allowances bound the actual source computation at every public key. -/
theorem UnrestrictedAdversary.query_allowances (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    (∀ pk, IsQueryBoundP (adversary.source pk) (fun i => queryKind i = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source pk) (fun i => queryKind i = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source pk) (fun i => Sum.isRight i = true) queries.sign) := by
  simpa only [CoCDHSecurityModel.queries_eq] using
    And.intro adversary.randomQueries (And.intro adversary.hashQueries adversary.signingQueries)

/-- Exact equality to the established lazy ROM game. -/
theorem cocdhEufCmaGame_eq (securityParameter : Nat) {queries : QueryAllowance}
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    cocdhEufCmaGame curve securityParameter adversary =
      CoCDH.Tight.blsEufLazyPK (F := curve.Scalar securityParameter) (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source := by
  exact Game.rom_eq_source curve securityParameter adversary.source

/-- Every unrestricted attacker within the declared resources and query allowances
obeys this EUF-CMA bound. `solverTime` charges the complete native Coron reduction,
including the caller, lazy oracle simulation, setup and extraction. For `s` signing
queries, `coronFactor s = ((s+1)⁻¹ * (s/(s+1))^s)⁻¹`, approximately `e*s`
for large `s` and exactly `1` when `s = 0`. -/
theorem Proofs.cocdh_security
    (curve : Model.PairingCurve) [model : CoCDHSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    let resources := model.parameters securityParameter queries
    𝒟[cocdhEufCmaGame curve securityParameter adversary] {true} ≤
      Model.coronFactor queries.sign *
        coCDHSuccessBound curve securityParameter queries resources.solverTime := by
  let resources := model.parameters securityParameter queries
  -- The existing probability reduction covers arbitrary messages and group outputs.
  have probabilityBound := CoCDH.Proofs.security_arbitrary_messages
    resources.generator resources.keyGenerator resources.queries.sign adversary.source
    resources.generates resources.pairingInjective (fun r => adversary.signingQueries (r • resources.keyGenerator))
  -- Build the native executable and derive its code/time bounds from primitive contracts.
  have fits := GeneralCoCDH.reduction_within resources adversary
  have solverBound : Model.coCDHAdvantage resources.generator resources.keyGenerator
      (CoCDH.coronReductionLazyPK (F := curve.Scalar securityParameter) resources.queries.sign
        (BLS.ROM.cacheForgeryPK adversary.source)) ≤
      coCDHSuccessBound curve securityParameter queries resources.solverTime :=
    le_iSup_of_le _ (le_iSup_of_le fits le_rfl)
  simpa only [resources, cocdhEufCmaGame_eq, CoCDHSecurityModel.queries_eq,
    CoCDHSecurityModel.generator_eq, CoCDHSecurityModel.keyGenerator_eq] using
    probabilityBound.trans (mul_le_mul_right solverBound (Model.coronFactor resources.queries.sign))

end CoCDH

end BLS
