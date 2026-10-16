import Signatures.Proximity.Proofs.GeneralSecurity

/-! Proximity security. Fix the curve, security parameter, query allowances and
execution model, then quantify over the attacker. `Game.lean` contains the game
without machine contracts. Proofs and derived budgets stay in supporting files.

Below, `p` is the group order and `εDL` is the DLog success bound at the proved
reduction budget, in the same execution model. A hardness assumption makes it
small. The notation expands to the existing resource-indexed quantities.
The collision term is the actual source-game event; collisions are not rejected.
-/

namespace Proximity

section AGM

variable (curve : Model.PairingCurve) [AGMSecurityModel curve]
  (securityParameter dimension : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "εDL" => dlogSuccessBound curve securityParameter dimension queries (agmReductionTime curve securityParameter dimension queries)
local notation "EUFCMA" => agmEufCmaGame curve securityParameter dimension
local notation "Collision" => freshCollisionGame curve securityParameter dimension

/-- Every resource-bounded algebraic attacker satisfies this forgery bound. -/
theorem agm_security
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    𝒟[EUFCMA adversary] {true} ≤ 2 * εDL + 1 / p + 𝒟[Collision adversary] {true} :=
  Proofs.agm_security_common_budget curve securityParameter dimension queries adversary

end AGM

/-- Optional sharper refinement: give the two DLog solvers separate budgets. -/
theorem agm_security_two_budgets
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter dimension : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    let resources := model.parameters securityParameter dimension queries
    𝒟[agmEufCmaGame curve securityParameter dimension adversary] {true} ≤
      dlogSuccessBound curve securityParameter dimension queries resources.goodTime +
      dlogSuccessBound curve securityParameter dimension queries resources.badTime +
      1 / (curve.order securityParameter : ENNReal) +
      𝒟[freshCollisionGame curve securityParameter dimension adversary] {true} :=
  Proofs.agm_security curve securityParameter dimension queries adversary

end Proximity
