import Signatures.Proximity.GeneralSecurityModel
import Signatures.Proximity.Proofs.LazyAGMArbitrarySlots
import Signatures.Proximity.Proofs.Game

/-! Proofs for the public Proximity statements. The displayed games equal the
original source games exactly. The constructed Caliper implementations meet the derived
resources and therefore belong to the explicit DLog success supremum. -/

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
    let resources := model.parameters securityParameter dimension queries
    𝒟[agmEufCmaGame curve securityParameter dimension adversary] {true} ≤
      dlogSuccessBound curve securityParameter dimension queries resources.goodTime +
      dlogSuccessBound curve securityParameter dimension queries resources.badTime +
      1 / (curve.order securityParameter : ENNReal) +
      𝒟[freshCollisionGame curve securityParameter dimension adversary] {true} := by
  let resources := model.parameters securityParameter dimension queries
  have probabilityBound := LazyAGM.Proofs.security_arbitrary_slots
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.proofView (curve.generates securityParameter) (curve.pairingInjective securityParameter)
  obtain ⟨goodFits, badFits⟩ := WeightedCaliper.reductions_within resources adversary
  have goodBound : Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
      (Model.LazyAGM.WeightedReduction.goodReductionList (LazyAGM.terms) adversary.proofView) ≤
      dlogSuccessBound curve securityParameter dimension queries resources.goodTime :=
    le_iSup_of_le _ (le_iSup_of_le goodFits le_rfl)
  have badBound : Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
      (Model.LazyAGM.WeightedReduction.badReductionList (LazyAGM.terms) adversary.proofView) ≤
      dlogSuccessBound curve securityParameter dimension queries resources.badTime :=
    le_iSup_of_le _ (le_iSup_of_le badFits le_rfl)
  have sourceBound := Model.DirectAGM.game_le (Gₜ := curve.TargetGroup securityParameter) LazyAGM.terms (fun _ _ => True)
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source
  simpa only [WeightedCaliper.AlgebraicAdversary.proofView, resources, agmEufCmaGame_eq, freshCollisionGame_eq,
    Model.PairingCurve.order] using
    sourceBound.trans (probabilityBound.trans (add_le_add (add_le_add (add_le_add goodBound badBound) le_rfl) le_rfl))

theorem dlogSuccessBound_mono (securityParameter dimension : Nat) (queries : QueryAllowance) :
    Monotone (dlogSuccessBound curve securityParameter dimension queries) := by
  intro time largerTime ht
  let resources := model.parameters securityParameter dimension queries
  exact CaliperBackend.dlogSuccessBound_mono resources.layout.port
    resources.layout.goodSetup.challenge resources.scalar
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) le_rfl le_rfl ht

theorem Proofs.agm_security_common_budget
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter dimension : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    𝒟[agmEufCmaGame curve securityParameter dimension adversary] {true} ≤
      2 * dlogSuccessBound curve securityParameter dimension queries
        (agmReductionTime curve securityParameter dimension queries) +
      1 / (curve.order securityParameter : ENNReal) +
      𝒟[freshCollisionGame curve securityParameter dimension adversary] {true} := by
  let resources := model.parameters securityParameter dimension queries
  have goodBound := dlogSuccessBound_mono curve securityParameter dimension queries
    (Nat.le_max_left resources.goodTime resources.badTime)
  have badBound := dlogSuccessBound_mono curve securityParameter dimension queries
    (Nat.le_max_right resources.goodTime resources.badTime)
  have bound := (Proofs.agm_security curve securityParameter dimension queries adversary).trans
    (add_le_add (add_le_add (add_le_add goodBound badBound) le_rfl) le_rfl)
  simpa only [two_mul, agmReductionTime, resources] using bound

end Proximity
