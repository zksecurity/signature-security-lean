import Signatures.Schnorr.Proofs.GeneralSecurity
import Signatures.Schnorr.Proofs.GeneralROMSecurity
import Signatures.Schnorr.Proofs.GeneralNonzeroROMSecurity
import Signatures.Schnorr.ArithmeticStatement

/-! Schnorr security. Fix the curve, security parameter, query allowances and
execution model, then quantify over the attacker. The independent `Game.lean`
shows key generation, oracle interaction, verification and freshness.

`p` is the group order; `qH` and `qS` count hash and signing calls. Each `εDL`
is DLog success at that route's complete proved reduction budget, including
replay for ROM. The local notation expands to the resource-indexed definition;
a hardness assumption makes it small. ROM requires no algebraic explanations.
Proofs, cost formulas and execution contracts remain in supporting files. -/

namespace Schnorr

section ROM

variable (curve : Model.CyclicCurve) [ROMSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "qH" => (queries.hash : ENNReal)
local notation "qS" => (queries.sign : ENNReal)
local notation "εDL" => romDLogSuccessBound curve securityParameter queries
  (romReductionTime curve securityParameter queries)
local notation "EUFCMA" => romEufCmaGame curve securityParameter

/-- Full-field signing nonces. The real exponent 1/2 is a square root. -/
theorem rom_security
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ qS * (qS + qH) * p⁻¹ +
      (qH + 1) * p⁻¹ + ((qH + 1) * εDL) ^ (1 / 2 : ℝ) :=
  Proofs.rom_security curve securityParameter queries adversary

end ROM

section NonzeroROM

variable (curve : Model.CyclicCurve) [NonzeroNonce.ROMSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "qH" => (queries.hash : ENNReal)
local notation "qS" => (queries.sign : ENNReal)
local notation "εDL" => NonzeroNonce.romDLogSuccessBound curve securityParameter queries
  (NonzeroNonce.romReductionTime curve securityParameter queries)
local notation "EUFCMA" => NonzeroNonce.romEufCmaGame curve securityParameter
local notation "pMinusOne" => ((curve.order securityParameter - 1 : Nat) : ENNReal)

/-- Nonzero signing nonces: the signing-loss denominator is p−1; the fork denominator is p. -/
theorem NonzeroNonce.rom_security
    (adversary : NonzeroNonce.UnrestrictedAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ qS * (qS + qH) * pMinusOne⁻¹ +
      (qH + 1) * p⁻¹ + ((qH + 1) * εDL) ^ (1 / 2 : ℝ) :=
  NonzeroNonce.Proofs.rom_security curve securityParameter queries adversary

end NonzeroROM

section AGM

variable (curve : Model.CyclicCurve) [AGMSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "qH" => (queries.hash : ENNReal)
local notation "qS" => (queries.sign : ENNReal)
local notation "εDL" => dlogSuccessBound curve securityParameter queries
  (agmReductionTime curve securityParameter queries)
local notation "EUFCMA" => agmEufCmaGame curve securityParameter

/-- Algebraic requests and output; arbitrary internal computation within the resource limits. -/
theorem agm_security
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ εDL + (qH + 1) * p⁻¹ + qS * (qS + qH) * p⁻¹ :=
  Proofs.agm_security curve securityParameter queries adversary

end AGM

end Schnorr
