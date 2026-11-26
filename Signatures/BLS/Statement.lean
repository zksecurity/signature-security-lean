import Proofs.BLS.GeneralSecurity
import Signatures.BLS.CaliperAGMFamilyStatement
import Signatures.BLS.CaliperCoCDHFamilyStatement
import Proofs.BLS.CaliperCoCDHCaller
import Signatures.BLS.ArithmeticStatement

/-! BLS security. Fix the curve, security parameter, query allowances and
execution model, then quantify over the attacker. `Game.lean` contains the game
without machine contracts. Proofs and derived budgets stay in supporting files.

Below, `p` is the group order. Each bound is the success of the named reductions
built from the attacker, in the standard (1,1)-DLog or co-CDH experiment; a
companion theorem places each reduction within the proved Caliper budget, so a
hardness assumption at that budget makes the bound small.
-/

namespace BLS

section AGM

variable (curve : Model.PairingCurve) [AGMSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter
local notation "EUFCMA" => agmEufCmaGame curve securityParameter

/-- Every algebraic attacker satisfies this forgery bound, in terms of the
`(1,1)`-DLog success of the two reductions built from it. -/
theorem agm_security
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤
      𝒟[AlgebraicGroupModel.dlog11Exp g₁ g₂ (agmGoodReduction curve adversary)] {true} +
      𝒟[AlgebraicGroupModel.dlog11Exp g₁ g₂ (agmBadReduction curve adversary)] {true} + 1 / p :=
  Proofs.agm_security curve securityParameter queries adversary

/-- The good reduction is Caliper code within the common derived code, memory and time budget. -/
theorem agm_good_reduction_within
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLog11SolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (agmGoodReduction curve adversary) :=
  Proofs.agm_good_reduction_within curve securityParameter queries adversary

/-- The bad reduction is Caliper code within the same budget. -/
theorem agm_bad_reduction_within
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLog11SolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (agmBadReduction curve adversary) :=
  Proofs.agm_bad_reduction_within curve securityParameter queries adversary

end AGM

section CoCDH

variable (curve : Model.PairingCurve) [CoCDHSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

-- The Coron factor depends only on signing calls; at zero calls it is one.
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter
local notation "EUFCMA" => cocdhEufCmaGame curve securityParameter

/-- Every unrestricted attacker satisfies this ROM bound, in terms of the co-CDH
success of Coron's reduction built from it. -/
theorem cocdh_security
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤
      Model.coronFactor queries.sign * 𝒟[CoCDH.coCDHExp g₁ g₂ (cocdhReduction curve adversary)] {true} :=
  Proofs.cocdh_security curve securityParameter queries adversary

/-- That reduction is Caliper code within its complete derived code, memory and time budget. -/
theorem cocdh_reduction_within
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    CoCDHSolverWithin curve securityParameter queries (cocdhReductionTime curve securityParameter queries)
      (cocdhReduction curve adversary) :=
  Proofs.cocdh_reduction_within curve securityParameter queries adversary

end CoCDH

end BLS
