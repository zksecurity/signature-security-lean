import Signatures.Proximity.GeneralSecurityModel
import Signatures.Proximity.Proofs.GeneralAGM

/-! Proofs for the public Proximity statements. The displayed games equal the
original source games exactly. The native implementations meet the derived
resources and therefore belong to the explicit DLog success supremum. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM

namespace Proximity

universe v w x

variable (curve : Model.PairingCurve) [model : AGMSecurityModel.{v, w, x} curve]

theorem AlgebraicAdversary.query_allowances (securityParameter dimension : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => General.queryKind i = 0) queries.random) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => General.queryKind i = 1) queries.hash) ∧
    (∀ pk, IsQueryBoundP (adversary.source.main pk) (fun i => General.queryKind i = 2) queries.sign) := by
  simpa only [AGMSecurityModel.queries_eq] using
    And.intro adversary.randomQueries (And.intro adversary.hashQueries adversary.signingQueries)

theorem agmEufCmaGame_eq (securityParameter dimension : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    agmEufCmaGame curve securityParameter dimension adversary =
      LazyAGM.game (Gₜ := curve.TargetGroup securityParameter)
        (curve.generator securityParameter) (curve.keyGenerator securityParameter) adversary.source := by
  classical
  simp only [agmEufCmaGame, Game.agm, LazyAGM.game, Model.LazyAGM.game, Model.LazyAGM.experiment, true_and]
  congr! 6
  split <;> split <;> simp_all

theorem freshCollisionGame_eq (securityParameter dimension : Nat) {queries : QueryAllowance}
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    freshCollisionGame curve securityParameter dimension adversary =
      LazyAGM.collisionGame (curve.keyGenerator securityParameter) adversary.source := by
  classical
  simp only [freshCollisionGame, Game.collision, LazyAGM.collisionGame, LazyAGM.collisionExperiment, LazyAGM.Collision]
  congr! 8
  exact decide_eq_decide.mpr Iff.rfl

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
    resources.generator resources.keyGenerator adversary.source resources.generates resources.pairingInjective
  obtain ⟨goodFits, badFits⟩ := GeneralAGM.reductions_within resources adversary
  have goodBound : Model.dlog11Advantage resources.generator resources.keyGenerator
      (Model.LazyAGM.WeightedReduction.goodReductionList (LazyAGM.terms) adversary.source) ≤
      dlogSuccessBound curve securityParameter dimension queries resources.goodTime :=
    le_iSup_of_le _ (le_iSup_of_le goodFits le_rfl)
  have badBound : Model.dlog11Advantage resources.generator resources.keyGenerator
      (Model.LazyAGM.WeightedReduction.badReductionList (LazyAGM.terms) adversary.source) ≤
      dlogSuccessBound curve securityParameter dimension queries resources.badTime :=
    le_iSup_of_le _ (le_iSup_of_le badFits le_rfl)
  simpa only [resources, agmEufCmaGame_eq, freshCollisionGame_eq, AGMSecurityModel.generator_eq, AGMSecurityModel.keyGenerator_eq,
    Model.PairingCurve.order] using
    probabilityBound.trans (add_le_add (add_le_add (add_le_add goodBound badBound) le_rfl) le_rfl)

theorem dlogSuccessBound_mono (securityParameter dimension : Nat) (queries : QueryAllowance) :
    Monotone (dlogSuccessBound curve securityParameter dimension queries) := by
  intro time largerTime ht
  let resources := model.parameters securityParameter dimension queries
  refine iSup_le fun solver => iSup_le fun fits => ?_
  have largerFits : NativeSolver.dlogWithin
      resources.rep resources.backend resources.descriptionSizes resources.factor resources.description
      resources.generator resources.keyGenerator resources.inputWidth resources.solverCode largerTime solver :=
    ⟨fits.1, Within.mono resources.backend resources.descriptionSizes resources.factor resources.description
      fits.2 le_rfl ht⟩
  exact le_iSup_of_le solver (le_iSup_of_le largerFits le_rfl)

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
