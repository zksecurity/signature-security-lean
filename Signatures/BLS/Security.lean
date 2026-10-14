import Signatures.BLS.SecurityModel

/-! Given a curve, security parameter, query allowances, and any algebraic
adversary in the declared execution model, the probability of forging a BLS
signature is at most the two DLog bounds plus the inverse scalar-field order.

The named bounds use the complete, proved reduction budgets. The model and
adversary definitions expose their resource assumptions in `SecurityModel.lean`. -/

open OracleComp

namespace BLS

/-- BLS EUF-CMA security in the algebraic group and random-oracle models. -/
theorem security
    (curve : Model.PairingCurve) [SecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[eufCmaGame curve securityParameter adversary] {true} ≤
      goodDLogBound curve securityParameter queries +
      badDLogBound curve securityParameter queries +
      1 / (curve.order securityParameter : ENNReal) := by
  have bound := GeneralAGM.security (SecurityModel.parameters securityParameter queries) adversary
  simpa only [eufCmaGame, goodDLogBound, badDLogBound, Model.PairingCurve.order,
    GeneralAGM.Parameters.securityBound, SecurityModel.generator_eq, SecurityModel.keyGenerator_eq]
    using bound

end BLS
