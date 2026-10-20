import Signatures.OOPS.GeneralSecurityModel
import Signatures.OOPS.Proofs.LazyAGMArbitraryTopics
import Signatures.OOPS.Proofs.Game

/-! Proofs for the public OOPS statements. The displayed games equal the
original source games exactly. The constructed Caliper implementations meet the derived
resources and therefore belong to the explicit DLog success supremum. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime

namespace OOPS

variable (curve : Model.PairingCurve) [model : AGMSecurityModel curve]

theorem AlgebraicAdversary.query_allowances (securityParameter degree : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => BLS.queryKind i.value.data = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => BLS.queryKind i.value.data = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => BLS.queryKind i.value.data = 2) queries.sign) := by
  exact ⟨adversary.randomQueries, adversary.hashQueries, adversary.signingQueries⟩

theorem agmEufCmaGame_eq (securityParameter degree : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    agmEufCmaGame curve securityParameter degree adversary =
      Model.DirectAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (LazyAGM.terms degree) (LazyAGM.admissible degree)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source := by
  exact Game.agm_eq_source curve securityParameter degree adversary.source

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
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) degree adversary.proofView (curve.generates securityParameter) (curve.pairingInjective securityParameter)
  rw [LazyAGM.game_eq_of_decidableEq] at probabilityBound
  obtain ⟨goodFits, badFits⟩ := WeightedCaliper.reductions_within resources adversary
  have goodBound : Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
      (Model.LazyAGM.WeightedReduction.goodReductionList (LazyAGM.terms degree) adversary.proofView) ≤
      dlogSuccessBound curve securityParameter degree queries resources.goodTime :=
    le_iSup_of_le _ (le_iSup_of_le goodFits le_rfl)
  have badBound : Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
      (Model.LazyAGM.WeightedReduction.badReductionList (LazyAGM.terms degree) adversary.proofView) ≤
      dlogSuccessBound curve securityParameter degree queries resources.badTime :=
    le_iSup_of_le _ (le_iSup_of_le badFits le_rfl)
  have sourceBound := Model.DirectAGM.game_le (Gₜ := curve.TargetGroup securityParameter) (LazyAGM.terms degree) (LazyAGM.admissible degree)
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source
  simpa only [WeightedCaliper.AlgebraicAdversary.proofView, resources, agmEufCmaGame_eq,
    Model.PairingCurve.order] using
    sourceBound.trans (probabilityBound.trans (add_le_add (add_le_add goodBound badBound) le_rfl))

theorem dlogSuccessBound_mono (securityParameter degree : Nat) (queries : QueryAllowance) :
    Monotone (dlogSuccessBound curve securityParameter degree queries) := by
  intro time largerTime ht
  let resources := model.parameters securityParameter degree queries
  exact CaliperBackend.dlogSuccessBound_mono resources.layout.port
    resources.layout.goodSetup.challenge resources.scalar
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) le_rfl le_rfl ht

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
