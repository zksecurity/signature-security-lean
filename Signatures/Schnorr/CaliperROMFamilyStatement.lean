import Signatures.Schnorr.Proofs.CaliperROMFamily

/-! Asymptotic security for the public ordinary-ROM Schnorr Caliper model.
Polynomial component allowances give a polynomial replaying reduction. Caliper
DLog hardness and negligible inverse group order then give negligible forgery. -/
namespace Schnorr
open OracleComp OracleSpec

/-- Unrestricted attacker families within polynomial Caliper allowances have
negligible EUF-CMA success under nonuniform Caliper DLog hardness and sufficient
group growth. Complete-solver resources are derived, not assumed. -/
theorem rom_security_asymptotic
    (curve : Model.CyclicCurve) [model : ROMSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, UnrestrictedAdversary curve n (queries n))
    (resources : CaliperROM.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : CaliperROM.Family.dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => (curve.order n : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[romEufCmaGame curve n (adversary n)] {true}) :=
  CaliperROM.Family.Proofs.security curve queries adversary resources hardness fieldGrowth

end Schnorr
