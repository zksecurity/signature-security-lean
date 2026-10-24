import Proofs.Schnorr.CaliperNonzeroROMFamily

/-! Asymptotic security for the public nonzero-nonce Schnorr ROM Caliper model. -/
namespace Schnorr.NonzeroNonce
open OracleComp OracleSpec

/-- Unrestricted nonzero-nonce attacker families within polynomial Caliper
allowances have negligible EUF-CMA success under nonuniform Caliper DLog
hardness and sufficient group growth. -/
theorem rom_security_asymptotic
    (curve : Model.CyclicCurve) [model : ROMSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, UnrestrictedAdversary curve n (queries n))
    (resources : CaliperROM.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : CaliperROM.Family.dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => (curve.order n : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[romEufCmaGame curve n (adversary n)] {true}) :=
  CaliperROM.Family.Proofs.nonzero_security curve queries adversary resources hardness fieldGrowth

end Schnorr.NonzeroNonce
