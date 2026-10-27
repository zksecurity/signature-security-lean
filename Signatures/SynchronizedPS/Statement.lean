import Proofs.SynchronizedPS.Security

/-! Synchronized Pointcheval–Sanders security. Fix the curve, security parameter and a finite
set of periods, then quantify over the algebraic attacker. `Game.lean` contains the game;
`Spec/Reduction.lean` the three `(1,1)`-DLog solvers, each a straight-line program that runs the
attacker once. Below, `p` is the group order and `ε B` is the solver `B`'s DLog success at the
curve's generators; a hardness assumption makes it small. The reductions are not yet costed in an
execution model, so this statement names them rather than a budgeted success bound. -/

namespace SynchronizedPS

section AGM

variable (curve : Model.PairingCurve) (securityParameter : Nat) {Period : Type}
  [DecidableEq Period] [Fintype Period]

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "ε" => Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
local notation "EUFCMA" => Game.agm curve securityParameter

/-- Every algebraic attacker satisfies this forgery bound: one DLog solver per place the challenge
can hide (the first key, the second key, the period hashes), plus the hidden-slope collision. -/
theorem agm_security (adversary : Game.AlgebraicAdversary curve securityParameter (Period := Period)) :
    𝒟[EUFCMA adversary] {true} ≤
      ε (Reduction.challengeInX adversary) + ε (Reduction.challengeInY adversary) +
        ε (Reduction.challengeInHashes adversary) + 1 / p :=
  Proofs.agm_security curve securityParameter adversary

end AGM

end SynchronizedPS
