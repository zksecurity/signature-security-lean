import Signatures.OOPS.GeneralSecurityModel
import Proofs.OOPS.LazyAGMArbitraryTopics
import Proofs.OOPS.Game

/-! Proofs for the public OOPS statements. The displayed games equal the
original source games exactly. The bound names the two constructed DLog
reductions, and their Caliper implementations meet the derived resources. -/

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
    𝒟[agmEufCmaGame curve securityParameter degree adversary] {true} ≤
      𝒟[AlgebraicGroupModel.dlog11Exp (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (agmGoodReduction curve adversary)] {true} +
      𝒟[AlgebraicGroupModel.dlog11Exp (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (agmBadReduction curve adversary)] {true} +
      1 / (curve.order securityParameter : ENNReal) := by
  have probabilityBound := LazyAGM.Proofs.security_arbitrary_topics
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) degree adversary.proofView (curve.generates securityParameter) (curve.pairingInjective securityParameter)
  rw [LazyAGM.game_eq_of_decidableEq] at probabilityBound
  have sourceBound := Model.DirectAGM.game_le (Gₜ := curve.TargetGroup securityParameter) (LazyAGM.terms degree) (LazyAGM.admissible degree)
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source
  simpa only [WeightedCaliper.AlgebraicAdversary.proofView, agmEufCmaGame_eq,
    agmGoodReduction, agmBadReduction, Model.PairingCurve.order, Model.dlog11Advantage] using
    sourceBound.trans probabilityBound

theorem Proofs.agm_good_reduction_within
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter degree : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    DLog11SolverWithin curve securityParameter degree queries (agmReductionTime curve securityParameter degree queries)
      (agmGoodReduction curve adversary) :=
  ((WeightedCaliper.reductions_within (model.parameters securityParameter degree queries) adversary).1).mono
    le_rfl le_rfl (Nat.le_max_left _ _)

theorem Proofs.agm_bad_reduction_within
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter degree : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    DLog11SolverWithin curve securityParameter degree queries (agmReductionTime curve securityParameter degree queries)
      (agmBadReduction curve adversary) :=
  ((WeightedCaliper.reductions_within (model.parameters securityParameter degree queries) adversary).2).mono
    le_rfl le_rfl (Nat.le_max_right _ _)

end OOPS
