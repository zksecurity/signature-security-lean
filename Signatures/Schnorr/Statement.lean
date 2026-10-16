import Signatures.Schnorr.Proofs.GeneralSecurity
import Signatures.Schnorr.Proofs.GeneralROMSecurity
import Signatures.Schnorr.Proofs.GeneralNonzeroROMSecurity
import Signatures.Schnorr.ArithmeticStatement

/-! Schnorr security: given a curve, security parameter, query allowances and
an attacker, bound the probability of forging on an unsigned message. The ROM
route allows unrestricted computation; the AGM route requires algebraic outputs.

The AGM bound is DLog success at the proved reduction time, plus `(qH+1)/|F|` and
`qS*(qS+qH)/|F|`. `𝒟[game] {true}` is the probability that the game accepts.
The game uses full-field nonces and one lazy oracle shared by hashing, signing
and final verification. Its full definition is in `GeneralSecurityModel.lean`.

The DLog term is a supremum over executable solvers in the same fixed backend,
at the derived input/code/time bounds. A hardness assumption makes it small.
The model fixes local operation/encoding contracts and attacker resource limits;
the reduction's complete cost is proved from them. The attacker supplies its
own implemented general local code and resource evidence; the AGM route additionally
requires algebraic outputs.

Proofs are in `Proofs/GeneralSecurity.lean` and `Proofs/GeneralAGM.lean`.
The supporting contracts are in `GeneralAGMParameters.lean`. The existing
arithmetic-source ROM theorem remains available through `ArithmeticStatement.lean`;
the derived AGM polynomial-family corollary is in `GeneralAGMFamilyStatement.lean`.
The general ROM theorem derives the entire replaying solver's runtime and stored
code. Its direct bound is signing loss plus `(qH+1)/|F|` plus the square root of
`(qH+1)` times DLog success at the derived budget. The original quadratic bound
remains in `Proofs/GeneralROM.lean`; public ROM proofs and inspectable definitions
are in `Proofs/GeneralROMSecurity.lean` and `GeneralROMSecurityModel.lean`.
Its nonuniform polynomial-family corollary is in `GeneralROMFamilyStatement.lean`.
The separate `NonzeroNonce.rom_security` theorem uses nonzero signing nonces;
its signing loss has denominator `|F|-1`. Its original contracts and proofs are
in `GeneralNonzeroROMParameters.lean` and `Proofs/GeneralNonzeroROM.lean`; the
family endpoint is in `GeneralNonzeroROMFamilyStatement.lean`. -/

namespace Schnorr

/-- Every unrestricted implemented attacker within the declared resource and
query allowances has ordinary-ROM forgery probability bounded by DLog success
and the original simulation/forking losses. The real exponent `1/2` is a square root. -/
theorem rom_security
    (curve : Model.CyclicCurve) [ROMSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[romEufCmaGame curve securityParameter adversary] {true} ≤
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * (curve.order securityParameter : ENNReal)⁻¹ +
      (queries.hash + 1 : ENNReal) * (curve.order securityParameter : ENNReal)⁻¹ +
      ((queries.hash + 1 : ENNReal) *
        romDLogSuccessBound curve securityParameter queries (romReductionTime curve securityParameter queries)) ^ (1 / 2 : ℝ) :=
  Proofs.rom_security curve securityParameter queries adversary

/-- Every unrestricted implemented attacker within the declared resource and
query allowances has nonzero-nonce ROM forgery probability bounded by DLog success
and the original simulation/forking losses, with signing denominator `|F|-1`.
The real exponent `1/2` is a square root. -/
theorem NonzeroNonce.rom_security
    (curve : Model.CyclicCurve) [NonzeroNonce.ROMSecurityModel curve]
    (securityParameter : Nat)
    (queries : QueryAllowance)
    (adversary : NonzeroNonce.UnrestrictedAdversary curve securityParameter queries) :
    𝒟[NonzeroNonce.romEufCmaGame curve securityParameter adversary] {true} ≤
      (queries.sign : ENNReal) * (queries.sign + queries.hash) * ((curve.order securityParameter - 1 : Nat) : ENNReal)⁻¹ +
      (queries.hash + 1 : ENNReal) * (curve.order securityParameter : ENNReal)⁻¹ +
      ((queries.hash + 1 : ENNReal) *
        NonzeroNonce.romDLogSuccessBound curve securityParameter queries (NonzeroNonce.romReductionTime curve securityParameter queries)) ^ (1 / 2 : ℝ) :=
  NonzeroNonce.Proofs.rom_security curve securityParameter queries adversary

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
