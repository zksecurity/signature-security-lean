import Signatures.OOPS.Proofs.GeneralSecurity

/-! OOPS security. Fix the curve, security parameter, query allowances and
execution model, then quantify over the attacker. `Game.lean` contains the game
without machine contracts. Proofs and derived budgets stay in supporting files.

Below, `p` is the group order and `εDL` is the DLog success bound at the proved
reduction budget, in the same execution model. A hardness assumption makes it
small. The notation expands to the existing resource-indexed quantities.
The game also checks at most `degree` distinct signed messages on the forged topic.
-/

namespace OOPS

section AGM

variable (curve : Model.PairingCurve) [AGMSecurityModel curve]
  (securityParameter degree : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "εDL" => dlogSuccessBound curve securityParameter degree queries (agmReductionTime curve securityParameter degree queries)
local notation "EUFCMA" => agmEufCmaGame curve securityParameter degree

/-- Every resource-bounded algebraic attacker satisfies this forgery bound. -/
theorem agm_security
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    𝒟[EUFCMA adversary] {true} ≤ 2 * εDL + 1 / p :=
  Proofs.agm_security_common_budget curve securityParameter degree queries adversary

end AGM

/-- Optional sharper refinement: give the two DLog solvers separate budgets. -/
theorem agm_security_two_budgets
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter degree : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    let resources := model.parameters securityParameter degree queries
    𝒟[agmEufCmaGame curve securityParameter degree adversary] {true} ≤
      dlogSuccessBound curve securityParameter degree queries resources.goodTime +
      dlogSuccessBound curve securityParameter degree queries resources.badTime +
      1 / (curve.order securityParameter : ENNReal) :=
  Proofs.agm_security curve securityParameter degree queries adversary

end OOPS
