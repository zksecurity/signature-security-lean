import Signatures.SynchronizedPS.SecurityModel
import Proofs.SynchronizedPS.Game
import Proofs.SynchronizedPS.PeriodTransport

/-! Proofs for the budgeted synchronized PS statement. The native game is bounded by the
coefficient game, which the four wrapped weighted solvers bound for any period type
(`PeriodTransport.lean`); each is, at the curve's generators, an executed Caliper solver within
the derived budgets, so it belongs to the explicit DLog success supremum. -/

open OracleComp OracleSpec
open Signatures.Runtime

namespace SynchronizedPS

variable (curve : Model.PairingCurve) [model : AGMSecurityModel curve]

theorem Proofs.agm_security_budgeted (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    let resources := model.parameters securityParameter queries
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      dlogSuccessBound curve securityParameter queries resources.goodTime₁ +
      dlogSuccessBound curve securityParameter queries resources.badTime₁ +
      dlogSuccessBound curve securityParameter queries resources.goodTime₂ +
      dlogSuccessBound curve securityParameter queries resources.badTime₂ +
      2 / (curve.order securityParameter : ENNReal) := by
  intro resources
  have game := Game.agm_le curve securityParameter adversary.source
  have wrapped := Transport.security_wrapped (Gₜ := curve.TargetGroup securityParameter)
    (Proofs.view adversary.source (curve.generator securityParameter))
    (curve.generator securityParameter) (curve.keyGenerator securityParameter)
    (curve.generates securityParameter) (curve.pairingInjective securityParameter)
  have good₁ := adversary.good₁_advantage
  have bad₁ := adversary.bad₁_advantage
  have good₂ := adversary.good₂_advantage
  have bad₂ := adversary.bad₂_advantage
  exact game.trans (wrapped.trans (add_le_add (add_le_add (add_le_add (add_le_add good₁ bad₁) good₂) bad₂) le_rfl))

theorem dlogSuccessBound_mono (securityParameter : Nat) (queries : QueryAllowance) :
    Monotone (dlogSuccessBound curve securityParameter queries) := by
  intro time largerTime ht
  let resources := model.parameters securityParameter queries
  exact CaliperBackend.dlogSuccessBound_mono resources.outer.port resources.shape.challenge resources.outer.good.extraction.scalar
    (curve.generator securityParameter) (curve.keyGenerator securityParameter) le_rfl le_rfl ht

theorem Proofs.agm_security_common_budget (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      4 * dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries) +
      2 / (curve.order securityParameter : ENNReal) := by
  let resources := model.parameters securityParameter queries
  have mono := dlogSuccessBound_mono curve securityParameter queries
  have good₁ := mono (le_trans (le_max_left _ _) (le_max_left _ _) :
    resources.goodTime₁ ≤ agmReductionTime curve securityParameter queries)
  have bad₁ := mono (le_trans (le_max_right _ _) (le_max_left _ _) :
    resources.badTime₁ ≤ agmReductionTime curve securityParameter queries)
  have good₂ := mono (le_trans (le_max_left _ _) (le_max_right _ _) :
    resources.goodTime₂ ≤ agmReductionTime curve securityParameter queries)
  have bad₂ := mono (le_trans (le_max_right _ _) (le_max_right _ _) :
    resources.badTime₂ ≤ agmReductionTime curve securityParameter queries)
  have bound := (Proofs.agm_security_budgeted curve securityParameter queries adversary).trans
    (add_le_add (add_le_add (add_le_add (add_le_add good₁ bad₁) good₂) bad₂) le_rfl)
  have four : (4 : ENNReal) * dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries) =
      dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries) +
      dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries) +
      dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries) +
      dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries) := by ring
  rw [four]
  exact bound

end SynchronizedPS
