import Proofs.Schnorr.GeneralSecurity
import Proofs.Schnorr.GeneralROMSecurity
import Proofs.Schnorr.GeneralNonzeroROMSecurity
import Signatures.Schnorr.ArithmeticStatement
import Signatures.Schnorr.CaliperAGMFamilyStatement
import Signatures.Schnorr.CaliperROMFamilyStatement
import Signatures.Schnorr.CaliperNonzeroROMFamilyStatement

/-! Schnorr security. Fix the curve, security parameter, query allowances and
execution model, then quantify over the attacker. The independent `Game.lean`
shows key generation, oracle interaction, verification and freshness.

`p` is the group order; `qH` and `qS` count hash and signing calls. Each bound
is stated in the DLog success of the route's named reduction built from the
attacker, with a companion `_reduction_within` theorem placing that reduction in
the fixed Caliper class at its derived code, total-memory and time budget (for ROM,
the replaying solver); a hardness assumption on that class makes the term small.
ROM requires no algebraic explanations. The polynomial-family theorems are in
`CaliperAGMFamilyStatement.lean`, `CaliperROMFamilyStatement.lean` and
`CaliperNonzeroROMFamilyStatement.lean`. The two ROM routes share one executed
replaying solver; only the executed signing branch's source law differs.
Proofs, cost formulas and execution contracts remain in supporting files. -/

namespace Schnorr

section ROM

variable (curve : Model.CyclicCurve) [ROMSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "qH" => (queries.hash : ENNReal)
local notation "qS" => (queries.sign : ENNReal)
local notation "g" => curve.generator securityParameter
local notation "EUFCMA" => romEufCmaGame curve securityParameter

/-- Full-field signing nonces. The real exponent 1/2 is a square root. -/
theorem rom_security
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ qS * (qS + qH) * p⁻¹ + (qH + 1) * p⁻¹ +
      ((qH + 1) * 𝒟[DiffieHellman.dlogExperiment g (romReduction curve adversary)] {true}) ^ (1 / 2 : ℝ) :=
  Proofs.rom_security curve securityParameter queries adversary

/-- That replaying reduction is Caliper code within the derived code, memory and time budget. -/
theorem rom_reduction_within
    (adversary : UnrestrictedAdversary curve securityParameter queries) :
    ROMDLogSolverWithin curve securityParameter queries (romReductionTime curve securityParameter queries)
      (romReduction curve adversary) :=
  Proofs.rom_reduction_within curve securityParameter queries adversary

end ROM

section NonzeroROM

variable (curve : Model.CyclicCurve) [NonzeroNonce.ROMSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "qH" => (queries.hash : ENNReal)
local notation "qS" => (queries.sign : ENNReal)
local notation "g" => curve.generator securityParameter
local notation "EUFCMA" => NonzeroNonce.romEufCmaGame curve securityParameter
local notation "pMinusOne" => ((curve.order securityParameter - 1 : Nat) : ENNReal)

/-- Nonzero signing nonces: the signing-loss denominator is p−1; the fork denominator is p. -/
theorem NonzeroNonce.rom_security
    (adversary : NonzeroNonce.UnrestrictedAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ qS * (qS + qH) * pMinusOne⁻¹ + (qH + 1) * p⁻¹ +
      ((qH + 1) * 𝒟[DiffieHellman.dlogExperiment g (NonzeroNonce.romReduction curve adversary)] {true}) ^
        (1 / 2 : ℝ) :=
  NonzeroNonce.Proofs.rom_security curve securityParameter queries adversary

/-- That replaying reduction is Caliper code within the derived code, memory and time budget. -/
theorem NonzeroNonce.rom_reduction_within
    (adversary : NonzeroNonce.UnrestrictedAdversary curve securityParameter queries) :
    NonzeroNonce.ROMDLogSolverWithin curve securityParameter queries
      (NonzeroNonce.romReductionTime curve securityParameter queries) (NonzeroNonce.romReduction curve adversary) :=
  NonzeroNonce.Proofs.rom_reduction_within curve securityParameter queries adversary

end NonzeroROM

section AGM

variable (curve : Model.CyclicCurve) [AGMSecurityModel curve]
  (securityParameter : Nat) (queries : QueryAllowance)

local notation "p" => (curve.order securityParameter : ENNReal)
local notation "qH" => (queries.hash : ENNReal)
local notation "qS" => (queries.sign : ENNReal)
local notation "g" => curve.generator securityParameter
local notation "EUFCMA" => agmEufCmaGame curve securityParameter

/-- Algebraic requests and output; arbitrary internal computation within the resource limits.
The forger's advantage is bounded by the DLog success of the reduction built from it. -/
theorem agm_security
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    𝒟[EUFCMA adversary] {true} ≤ 𝒟[DiffieHellman.dlogExperiment g (agmReduction curve adversary)] {true} +
      (qH + 1) * p⁻¹ + qS * (qS + qH) * p⁻¹ :=
  Proofs.agm_security curve securityParameter queries adversary

/-- That reduction is Caliper code within the derived code, memory and time budget. -/
theorem agm_reduction_within
    (adversary : AlgebraicAdversary curve securityParameter queries) :
    DLogSolverWithin curve securityParameter queries (agmReductionTime curve securityParameter queries)
      (agmReduction curve adversary) :=
  Proofs.agm_reduction_within curve securityParameter queries adversary

end AGM

end Schnorr
