import Signatures.Proximity.GeneralSecurityModel
import Proofs.Proximity.LazyAGMArbitrarySlots
import Proofs.Proximity.Game

/-! Proofs for the public Proximity statements. The displayed games equal the
original source games exactly. The bound names the two constructed DLog
reductions, and their Caliper implementations meet the derived resources. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime

namespace Proximity

variable (curve : Model.PairingCurve) [model : AGMSecurityModel curve]

theorem AlgebraicAdversary.query_allowances (securityParameter dimension : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => BLS.queryKind i.value.data = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => BLS.queryKind i.value.data = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main (Model.LazyAGM.Interactive.initialInput (curve.generator securityParameter) pk))
      (fun i => BLS.queryKind i.value.data = 2) queries.sign) := by
  exact ⟨adversary.randomQueries, adversary.hashQueries, adversary.signingQueries⟩

theorem agmEufCmaGame_eq (securityParameter dimension : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    agmEufCmaGame curve securityParameter dimension adversary =
      Model.DirectAGM.game (Gₜ := curve.TargetGroup securityParameter)
        LazyAGM.terms (fun _ _ => True)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source := by
  exact Game.agm_eq_source curve securityParameter dimension adversary.source

theorem freshCollisionGame_eq (securityParameter dimension : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    freshCollisionGame curve securityParameter dimension adversary =
      LazyAGM.collisionGame (curve.keyGenerator securityParameter)
        (Model.DirectAGM.ProofView.adversary (curve.generator securityParameter) adversary.source) := by
  exact Game.collision_eq_source curve securityParameter dimension adversary.source

theorem Proofs.agm_security
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter dimension : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    𝒟[agmEufCmaGame curve securityParameter dimension adversary] {true} ≤
      𝒟[AlgebraicGroupModel.dlog11Exp (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (agmGoodReduction curve adversary)] {true} +
      𝒟[AlgebraicGroupModel.dlog11Exp (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (agmBadReduction curve adversary)] {true} +
      1 / (curve.order securityParameter : ENNReal) +
      𝒟[freshCollisionGame curve securityParameter dimension adversary] {true} := by
  have probabilityBound := LazyAGM.Proofs.security_arbitrary_slots
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.proofView (curve.generates securityParameter) (curve.pairingInjective securityParameter)
  have sourceBound := Model.DirectAGM.game_le (Gₜ := curve.TargetGroup securityParameter) LazyAGM.terms (fun _ _ => True)
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source
  simpa only [WeightedCaliper.AlgebraicAdversary.proofView, agmEufCmaGame_eq, freshCollisionGame_eq,
    agmGoodReduction, agmBadReduction, Model.PairingCurve.order, Model.dlog11Advantage] using
    sourceBound.trans probabilityBound

theorem Proofs.agm_good_reduction_within
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter dimension : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    DLog11SolverWithin curve securityParameter dimension queries (agmReductionTime curve securityParameter dimension queries)
      (agmGoodReduction curve adversary) :=
  ((WeightedCaliper.reductions_within (model.parameters securityParameter dimension queries) adversary).1).mono
    le_rfl le_rfl (Nat.le_max_left _ _)

theorem Proofs.agm_bad_reduction_within
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter dimension : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    DLog11SolverWithin curve securityParameter dimension queries (agmReductionTime curve securityParameter dimension queries)
      (agmBadReduction curve adversary) :=
  ((WeightedCaliper.reductions_within (model.parameters securityParameter dimension queries) adversary).2).mono
    le_rfl le_rfl (Nat.le_max_right _ _)

end Proximity
