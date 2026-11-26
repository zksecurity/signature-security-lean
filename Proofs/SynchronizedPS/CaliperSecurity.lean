import Signatures.SynchronizedPS.SecurityModel
import Proofs.SynchronizedPS.Game
import Proofs.SynchronizedPS.PeriodTransport

/-! Proofs for the budgeted synchronized PS statement. The native game is bounded by the
coefficient game, which the four wrapped weighted solvers bound for any period type
(`PeriodTransport.lean`); at the curve's generators each has the advantage of an executed Caliper
solver, and each executed solver is within the derived budget. -/

open OracleComp OracleSpec
open Signatures.Runtime

namespace SynchronizedPS

variable (curve : Model.PairingCurve) [model : AGMSecurityModel curve]

theorem Proofs.agm_security_budgeted (securityParameter : Nat) (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    let ε := Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      ε (goodReduction₁ curve adversary) + ε (badReduction₁ curve adversary) +
      ε (goodReduction₂ curve adversary) + ε (badReduction₂ curve adversary) +
      2 / (curve.order securityParameter : ENNReal) := by
  intro ε
  have game := Game.agm_le curve securityParameter adversary.source
  have wrapped := Transport.security_wrapped (Gₜ := curve.TargetGroup securityParameter)
    (Proofs.view adversary.source (curve.generator securityParameter))
    (curve.generator securityParameter) (curve.keyGenerator securityParameter)
    (curve.generates securityParameter) (curve.pairingInjective securityParameter)
  rw [adversary.good₁_eq, adversary.bad₁_eq, adversary.good₂_eq, adversary.bad₂_eq] at wrapped
  exact game.trans wrapped

section Within

variable (securityParameter : Nat) (queries : QueryAllowance)
  (adversary : AlgebraicAdversary curve securityParameter queries)

theorem Proofs.agm_good₁_reduction_within :
    DLogSolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (goodReduction₁ curve adversary) :=
  adversary.caliperGood₁_within.mono le_rfl le_rfl (le_trans (le_max_left _ _) (le_max_left _ _))

theorem Proofs.agm_bad₁_reduction_within :
    DLogSolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (badReduction₁ curve adversary) :=
  adversary.caliperBad₁_within.mono le_rfl le_rfl (le_trans (le_max_right _ _) (le_max_left _ _))

theorem Proofs.agm_good₂_reduction_within :
    DLogSolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (goodReduction₂ curve adversary) :=
  adversary.caliperGood₂_within.mono le_rfl le_rfl (le_trans (le_max_left _ _) (le_max_right _ _))

theorem Proofs.agm_bad₂_reduction_within :
    DLogSolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (badReduction₂ curve adversary) :=
  adversary.caliperBad₂_within.mono le_rfl le_rfl (le_trans (le_max_right _ _) (le_max_right _ _))

end Within

end SynchronizedPS
