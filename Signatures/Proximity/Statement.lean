import Signatures.Proximity.Proofs.GeneralSecurity
import Signatures.Proximity.ArithmeticStatement

/-! Proximity AGM security for general implemented algebraic attackers. Given a
curve, security parameter, dimension, query allowances and adversary, bound the
probability of forging a valid fresh vector/slot pair.

The DLog bound is an explicit supremum over implementations in the same fixed
backend, at the proved input/code/time limits. The derived reduction time charges
dimension-dependent term generation, attacker execution, lazy queries and extraction.
The original function-vector/optional-coordinate game is preserved exactly.
Fresh collisions contribute their actual source-game probability; the game does
not reject them and this theorem does not assume they are negligible.

The model supplies individual primitive/encoding contracts and attacker limits,
with no finished-reduction efficiency premise. A hardness assumption is needed
to make the DLog term small. Definitions are in `GeneralSecurityModel.lean`,
and proofs are in `Proofs/GeneralSecurity.lean`. -/

namespace Proximity

theorem agm_security
    (curve : Model.PairingCurve) [AGMSecurityModel curve]
    (securityParameter dimension : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter dimension queries) :
    𝒟[agmEufCmaGame curve securityParameter dimension adversary] {true} ≤
      2 * dlogSuccessBound curve securityParameter dimension queries
        (agmReductionTime curve securityParameter dimension queries) +
      1 / (curve.order securityParameter : ENNReal) +
      𝒟[freshCollisionGame curve securityParameter dimension adversary] {true} :=
  Proofs.agm_security_common_budget curve securityParameter dimension queries adversary

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
