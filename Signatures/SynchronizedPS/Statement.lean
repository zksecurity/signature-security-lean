import Proofs.SynchronizedPS.Security
import Proofs.SynchronizedPS.CaliperSecurity

/-! Synchronized Pointcheval–Sanders security. Fix the curve and security parameter, then
quantify over the algebraic attacker. `Game.lean` contains the game; `Spec/Reduction.lean` the
three `(1,1)`-DLog solvers, each a straight-line program that runs the attacker once. Below, `p`
is the group order and `ε B` is the solver `B`'s DLog success at the curve's generators; a
hardness assumption makes it small. The first statement names the three solvers without costing
them; they sample a hash table over the periods, so it is stated for a finite period type. The
second fixes an execution model (`SecurityModel.lean`) and bounds the attacker by the success of
four executed Caliper solvers built from it: the two weighted schemes `x•H(t)` and `y•(m•H(t))`
with the other key known, each with its good and bad branch. Each solver is separately proved
within the derived code, memory and time budget. Its period type only needs decidable equality,
as for OOPS's topics. -/

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
local notation "ε" => Model.dlog11Advantage (curve.generator securityParameter) (curve.keyGenerator securityParameter)
local notation "EUFCMA" => agmEufCmaGame curve securityParameter
local notation "T" => agmReductionTime curve securityParameter queries

/-- Every resource-bounded algebraic attacker of the single honest signer satisfies this forgery
bound: four executed DLog solvers built from it plus two hidden-slope collisions. -/
theorem agm_security_budgeted (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤
      ε (goodReduction₁ curve adversary) + ε (badReduction₁ curve adversary) +
        ε (goodReduction₂ curve adversary) + ε (badReduction₂ curve adversary) + 2 / p :=
  Proofs.agm_security_budgeted curve securityParameter queries adversary

/-- Each of the four solvers is Caliper code within the derived code, memory and time budget. -/
theorem agm_good₁_reduction_within (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLogSolverWithin curve securityParameter queries T (goodReduction₁ curve adversary) :=
  Proofs.agm_good₁_reduction_within curve securityParameter queries adversary

theorem agm_bad₁_reduction_within (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLogSolverWithin curve securityParameter queries T (badReduction₁ curve adversary) :=
  Proofs.agm_bad₁_reduction_within curve securityParameter queries adversary

theorem agm_good₂_reduction_within (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLogSolverWithin curve securityParameter queries T (goodReduction₂ curve adversary) :=
  Proofs.agm_good₂_reduction_within curve securityParameter queries adversary

theorem agm_bad₂_reduction_within (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLogSolverWithin curve securityParameter queries T (badReduction₂ curve adversary) :=
  Proofs.agm_bad₂_reduction_within curve securityParameter queries adversary

end Caliper

end SynchronizedPS
