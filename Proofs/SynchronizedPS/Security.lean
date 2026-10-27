import Proofs.SynchronizedPS.Game

/-! Proof of the public synchronized PS statement: the native game is bounded by the coefficient
game, which the three explicit solvers bound at the curve's generators. -/

namespace SynchronizedPS

variable (curve : Model.PairingCurve) (securityParameter : Nat) {Period : Type}
  [DecidableEq Period] [Fintype Period]

theorem Proofs.agm_security (adversary : Game.AlgebraicAdversary curve securityParameter (Period := Period)) :
    𝒟[Game.agm curve securityParameter adversary] {true} ≤
      Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (Reduction.challengeInX adversary) +
      Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (Reduction.challengeInY adversary) +
      Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
        (Reduction.challengeInHashes adversary) +
      1 / (curve.order securityParameter : ENNReal) :=
  (Game.agm_le curve securityParameter adversary).trans
    (Proofs.security (Gₜ := curve.TargetGroup securityParameter) (curve.generator securityParameter)
      (curve.keyGenerator securityParameter) adversary (curve.generates securityParameter)
      (curve.pairingInjective securityParameter))

end SynchronizedPS
