import Proofs.SynchronizedPS.Security
import Proofs.SynchronizedPS.CaliperSecurity

/-! Synchronized Pointcheval–Sanders security. Fix the curve, security parameter and a finite
set of periods, then quantify over the algebraic attacker. `Game.lean` contains the game;
`Spec/Reduction.lean` the three `(1,1)`-DLog solvers, each a straight-line program that runs the
attacker once. Below, `p` is the group order and `ε B` is the solver `B`'s DLog success at the
curve's generators; a hardness assumption makes it small. The first statement names the three
solvers without costing them. The second fixes an execution model (`SecurityModel.lean`) and
bounds the attacker, who faces the single honest signer and reports no co-signer keys, by `εDL`,
the DLog success supremum at the proved budget of four executed Caliper solvers: the two weighted
schemes `x•H(t)` and `y•(m•H(t))` with the other key known, each with its good and bad branch. -/

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

section Caliper

variable (curve : Model.PairingCurve) [AGMSecurityModel curve] (securityParameter : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "εDL" => dlogSuccessBound curve securityParameter queries (agmReductionTime curve securityParameter queries)
local notation "EUFCMA" => agmEufCmaGame curve securityParameter

/-- Every resource-bounded algebraic attacker of the single honest signer satisfies this forgery
bound: four executed DLog solvers plus two hidden-slope collisions. -/
theorem agm_security_budgeted (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ 4 * εDL + 2 / p :=
  Proofs.agm_security_common_budget curve securityParameter queries adversary

end Caliper

end SynchronizedPS
