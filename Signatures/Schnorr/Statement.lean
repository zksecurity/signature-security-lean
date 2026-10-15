import Signatures.Schnorr.Proofs.GeneralSecurity
import Signatures.Schnorr.ArithmeticStatement

/-! Schnorr AGM security: given a curve, security parameter, query allowances
and an algebraic adversary, bound the probability of forging on an unsigned message.

The bound is DLog success at the proved reduction time, plus `(qH+1)/|F|` and
`qS*(qS+qH)/|F|`. `𝒟[game] {true}` is the probability that the game accepts.
The game uses full-field nonces and one lazy oracle shared by hashing, signing
and final verification. Its full definition is in `GeneralSecurityModel.lean`.

The DLog term is a supremum over executable solvers in the same fixed backend,
at the derived input/code/time bounds. A hardness assumption makes it small.
The model fixes local operation/encoding contracts and attacker resource limits;
the reduction's complete cost is proved from them. The attacker supplies its
own implemented general local code, resource evidence and algebraic outputs.

Proofs are in `Proofs/GeneralSecurity.lean` and `Proofs/GeneralAGM.lean`.
The supporting contracts are in `GeneralAGMParameters.lean`. The existing
arithmetic-source ROM theorem remains available through `ArithmeticStatement.lean`;
the derived AGM polynomial-family corollary is in `GeneralAGMFamilyStatement.lean`.
General-caller ROM replay remains separate work. -/

namespace Schnorr

/-- Any algebraic adversary within the declared resources and query allowances
has forgery probability bounded by DLog success and the original query losses. -/
theorem agm_security
    (curve : Model.CyclicCurve) [AGMSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[agmEufCmaGame curve securityParameter adversary] {true} ≤
      dlogSuccessBound curve securityParameter queries
        (agmReductionTime curve securityParameter queries) +
      (queries.hash + 1 : ENNReal) * (curve.order securityParameter : ENNReal)⁻¹ +
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * (curve.order securityParameter : ENNReal)⁻¹ :=
  Proofs.agm_security curve securityParameter queries adversary

end Schnorr
