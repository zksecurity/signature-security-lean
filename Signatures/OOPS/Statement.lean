import Signatures.OOPS.Proofs.GeneralSecurity
import Signatures.OOPS.ArithmeticStatement

/-! OOPS AGM security for general implemented algebraic attackers. Given a
curve, security parameter, degree, query allowances and adversary, bound the
probability of forging a valid fresh scalar/topic pair. Winning also requires at
most `degree` distinct signed scalar messages on the forged topic.

The DLog bound is an explicit supremum over implementations in the same fixed
backend, at the proved input/code/time limits. The reduction time includes
degree-dependent term generation, attacker execution, lazy queries and extraction.
The model fixes individual primitive/encoding contracts and attacker limits.
It does not assume a finished reduction is efficient. A hardness assumption is
needed to make the DLog term small. Inspect `GeneralSecurityModel.lean` for the
games and bounds, and `Proofs/GeneralSecurity.lean` for the proofs. -/

namespace OOPS

theorem agm_security
    (curve : Model.PairingCurve) [AGMSecurityModel curve]
    (securityParameter degree : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter degree queries) :
    𝒟[agmEufCmaGame curve securityParameter degree adversary] {true} ≤
      2 * dlogSuccessBound curve securityParameter degree queries
        (agmReductionTime curve securityParameter degree queries) +
      1 / (curve.order securityParameter : ENNReal) :=
  Proofs.agm_security_common_budget curve securityParameter degree queries adversary

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
