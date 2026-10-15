import Signatures.OOPS.GeneralSecurityModel
import Signatures.OOPS.Proofs.GeneralAGM

/-! Proofs for the public OOPS statements. The displayed games equal the
original source games exactly. The native implementations meet the derived
resources and therefore belong to the explicit DLog success supremum. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM

namespace OOPS

universe v w x

variable (curve : Model.PairingCurve) [model : AGMSecurityModel.{v, w, x} curve]

theorem AlgebraicAdversary.query_allowances (securityParameter degree : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => General.queryKind i = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => General.queryKind i = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => General.queryKind i = 2) queries.sign) := by
  simpa only [AGMSecurityModel.queries_eq] using
    And.intro adversary.randomQueries (And.intro adversary.hashQueries adversary.signingQueries)

theorem agmEufCmaGame_eq (securityParameter degree : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    agmEufCmaGame curve securityParameter degree adversary =
      LazyAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) degree adversary.source := by
  classical
  rw [LazyAGM.game_eq_of_decidableEq]
  simp only [agmEufCmaGame, Model.LazyAGM.game, Model.LazyAGM.experiment, LazyAGM.admissible]
  congr! 6
  split <;> split <;> simp_all

theorem Proofs.agm_security
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter degree : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    let resources := model.parameters securityParameter degree queries
    𝒟[agmEufCmaGame curve securityParameter degree adversary] {true} ≤
      dlogSuccessBound curve securityParameter degree queries resources.goodTime +
      dlogSuccessBound curve securityParameter degree queries resources.badTime +
      1 / (curve.order securityParameter : ENNReal) := by
  let resources := model.parameters securityParameter degree queries
  have probabilityBound := LazyAGM.Proofs.security_arbitrary_topics
    resources.generator resources.keyGenerator degree adversary.source resources.generates resources.pairingInjective
  obtain ⟨goodFits, badFits⟩ := GeneralAGM.reductions_within resources adversary
  have goodBound : Model.dlog11Advantage resources.generator resources.keyGenerator
      (Model.LazyAGM.WeightedReduction.goodReductionList (LazyAGM.terms degree) adversary.source) ≤
      dlogSuccessBound curve securityParameter degree queries resources.goodTime :=
    le_iSup_of_le _ (le_iSup_of_le goodFits le_rfl)
  have badBound : Model.dlog11Advantage resources.generator resources.keyGenerator
      (Model.LazyAGM.WeightedReduction.badReductionList (LazyAGM.terms degree) adversary.source) ≤
      dlogSuccessBound curve securityParameter degree queries resources.badTime :=
    le_iSup_of_le _ (le_iSup_of_le badFits le_rfl)
  simpa only [resources, agmEufCmaGame_eq, AGMSecurityModel.generator_eq, AGMSecurityModel.keyGenerator_eq,
    Model.PairingCurve.order] using
    probabilityBound.trans (add_le_add (add_le_add goodBound badBound) le_rfl)

theorem dlogSuccessBound_mono (securityParameter degree : Nat) (queries : QueryAllowance) :
    Monotone (dlogSuccessBound curve securityParameter degree queries) := by
  intro time largerTime ht
  let resources := model.parameters securityParameter degree queries
  refine iSup_le fun solver => iSup_le fun fits => ?_
  have largerFits : NativeSolver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.keyGenerator resources.inputWidth resources.solverCode largerTime solver :=
    ⟨fits.1, Within.mono resources.backend resources.descriptionSizes resources.factor resources.description
      fits.2 le_rfl ht⟩
  exact le_iSup_of_le solver (le_iSup_of_le largerFits le_rfl)

theorem Proofs.agm_security_common_budget
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter degree : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    𝒟[agmEufCmaGame curve securityParameter degree adversary] {true} ≤
      2 * dlogSuccessBound curve securityParameter degree queries
        (agmReductionTime curve securityParameter degree queries) +
      1 / (curve.order securityParameter : ENNReal) := by
  let resources := model.parameters securityParameter degree queries
  have goodBound := dlogSuccessBound_mono curve securityParameter degree queries
    (Nat.le_max_left resources.goodTime resources.badTime)
  have badBound := dlogSuccessBound_mono curve securityParameter degree queries
    (Nat.le_max_right resources.goodTime resources.badTime)
  have bound := (Proofs.agm_security curve securityParameter degree queries adversary).trans
    (add_le_add (add_le_add goodBound badBound) le_rfl)
  simpa only [two_mul, agmReductionTime, resources] using bound

end OOPS
