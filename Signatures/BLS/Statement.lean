import Signatures.BLS.Proofs.GeneralSecurity
import Signatures.BLS.ArithmeticStatement

/-! BLS security: given a curve, security parameter, query allowances and an
adversary, bound the probability of forging a valid signature on an unsigned message.

* AGM: forgery probability ≤ 2 × DLog success + 1 / group order.
* Unrestricted ROM: forgery probability ≤ Coron factor × co-CDH success.

`𝒟[game] {true}` is the probability that the game accepts the forgery. Hashing,
signing and verification share an initially empty lazy random oracle.
The success bounds are suprema over executable hardness solvers, with the same
fixed backend and derived input/code/time limits as the reductions. They need
hardness assumptions to be small. They are not extra assumptions that our
reductions are efficient.

`agmReductionTime` is the maximum of the two proved DLog reduction times;
`cocdhReductionTime` is the proved Coron reduction time. The sharper two-budget
AGM bound is also available below. The model fixes primitive/encoding contracts
and attacker resource limits; the adversary supplies its own implemented code,
resource proofs and query bounds. Its internal computation is unrestricted;
only the AGM route also requires algebraic group outputs.

Inspect these definitions in `GeneralSecurityModel.lean`, the component contracts
in `GeneralAGMParameters.lean` / `GeneralCoCDHParameters.lean`, and the proofs in
`Proofs/GeneralSecurity.lean`. Older arithmetic-source statements are in
`ArithmeticStatement.lean`. -/

namespace BLS

/-- Every algebraic adversary within the declared resources and query allowances
has forgery probability at most twice the `(1,1)`-DLog success bound plus `1/|F|`. -/
theorem agm_security
    (curve : Model.PairingCurve) [AGMSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      2 * dlogSuccessBound curve securityParameter queries
        (agmReductionTime curve securityParameter queries) +
      1 / (curve.order securityParameter : ENNReal) :=
  Proofs.agm_security_common_budget curve securityParameter queries adversary

/-- Every unrestricted adversary within the declared resources and query allowances
has forgery probability at most the Coron factor times the co-CDH success bound.
For `s` signing queries, `coronFactor s = ((s+1)⁻¹ * (s/(s+1))^s)⁻¹`;
in particular, `coronFactor 0 = 1`. -/
theorem cocdh_security
    (curve : Model.PairingCurve) [CoCDHSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[cocdhEufCmaGame curve securityParameter adversary] {true} ≤
      Model.coronFactor queries.sign *
        coCDHSuccessBound curve securityParameter queries
          (cocdhReductionTime curve securityParameter queries) :=
  Proofs.cocdh_security curve securityParameter queries adversary

/-- Sharper AGM bound using each reduction's own runtime. The good branch handles
a nonzero extraction denominator; the bad branch uses independent affine masks
for the zero-denominator case. The remaining probability loss is `1/|F|`. -/
theorem agm_security_two_budgets
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    let resources := model.parameters securityParameter queries
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      dlogSuccessBound curve securityParameter queries resources.goodTime +
      dlogSuccessBound curve securityParameter queries resources.badTime +
      1 / (curve.order securityParameter : ENNReal) :=
  Proofs.agm_security curve securityParameter queries adversary

end BLS
