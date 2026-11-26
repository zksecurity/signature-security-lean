import Proofs.OOPS.GeneralSecurity

/-! OOPS security. Fix the curve, security parameter, query allowances and
execution model, then quantify over the attacker. `Game.lean` contains the game
without machine contracts. Proofs and derived budgets stay in supporting files.

Below, `p` is the group order and `g₁, g₂` are the two generators of the
`(1,1)`-DLog game. The bound names the two reductions built from the attacker,
and separate theorems show both are Caliper code within the derived budget in the
same execution model, so a DLog hardness assumption at that budget makes them small.
The game also checks at most `degree` distinct signed messages on the forged topic.
-/

namespace OOPS

section AGM

variable (curve : Model.PairingCurve) [AGMSecurityModel curve]
  (securityParameter degree : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "g₁" => curve.generator securityParameter
local notation "g₂" => curve.keyGenerator securityParameter
local notation "T" => agmReductionTime curve securityParameter degree queries
local notation "EUFCMA" => agmEufCmaGame curve securityParameter degree

/-- Every resource-bounded algebraic attacker satisfies this forgery bound. -/
theorem agm_security
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    𝒟[EUFCMA adversary] {true} ≤
      𝒟[AlgebraicGroupModel.dlog11Exp g₁ g₂ (agmGoodReduction curve adversary)] {true} +
      𝒟[AlgebraicGroupModel.dlog11Exp g₁ g₂ (agmBadReduction curve adversary)] {true} + 1 / p :=
  Proofs.agm_security curve securityParameter degree queries adversary

/-- The first reduction is Caliper code within the derived code, memory and time budget. -/
theorem agm_good_reduction_within
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    DLog11SolverWithin curve securityParameter degree queries T (agmGoodReduction curve adversary) :=
  Proofs.agm_good_reduction_within curve securityParameter degree queries adversary

/-- So is the second. -/
theorem agm_bad_reduction_within
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    DLog11SolverWithin curve securityParameter degree queries T (agmBadReduction curve adversary) :=
  Proofs.agm_bad_reduction_within curve securityParameter degree queries adversary

end AGM

end OOPS
