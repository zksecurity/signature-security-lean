import Signatures.BLS.Proofs.GeneralSecurity
import Signatures.BLS.ArithmeticStatement

/-! BLS has two security routes:

* `agm_security`: an algebraic attacker has forgery probability at most the sum
  of two (1,1)-DLog success bounds and `1/|F|`.
* `cocdh_security`: an unrestricted attacker has forgery probability at most
  the Coron signing-query factor times a co-CDH success bound.

Both take a curve, security parameter, query allowances, and an attacker in a
fixed execution/resource model. `GeneralSecurityModel.lean` spells out the two
models, attacker contracts, actual EUF-CMA games, and hardness suprema. Hashing,
signing and final verification share an initially empty lazy random oracle;
winning means a valid signature on a message never signed.

The success bounds range over executable solvers at the reductions' derived
time, input and stored-code bounds. Their smallness requires the corresponding
hardness assumption. The operation/resource contracts are in
`GeneralAGMParameters.lean` and `GeneralCoCDHParameters.lean`.

Proofs are in `Proofs/GeneralSecurity.lean`. They construct each reduction's
resource certificate from component contracts before applying the probability
reduction and the supremum bound. Older arithmetic-source statements are in
`ArithmeticStatement.lean`. -/

namespace BLS

/-- Every algebraic attacker within the declared resources and query allowances obeys
this EUF-CMA bound. `goodTime` and `badTime` are the complete derived reduction times.
The good branch extracts from a nonzero denominator. The bad branch uses independent
affine masks to handle the zero-denominator case; the proof's remaining loss is `1/|F|`. -/
theorem agm_security
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

/-- Every unrestricted attacker within the declared resources and query allowances
obeys this EUF-CMA bound. `solverTime` charges the complete native Coron reduction,
including the caller, lazy oracle simulation, setup and extraction. For `s` signing
queries, `coronFactor s = ((s+1)⁻¹ * (s/(s+1))^s)⁻¹`, approximately `e*s`
for large `s` and exactly `1` when `s = 0`. -/
theorem cocdh_security
    (curve : Model.PairingCurve) [model : CoCDHSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    let resources := model.parameters securityParameter queries
    𝒟[cocdhEufCmaGame curve securityParameter adversary] {true} ≤
      Model.coronFactor queries.sign *
        coCDHSuccessBound curve securityParameter queries resources.solverTime :=
  Proofs.cocdh_security curve securityParameter queries adversary

end BLS
