import Signatures.BLS.Proofs.CaliperCoCDHFamily

/-! Asymptotic BLS co-CDH security in the fixed Caliper model. The complete
reduction's polynomial time, stored code and total memory follow from component
bounds. This is nonuniform security with ideal uniform sampling; conventional
machine coverage and CPU adequacy remain separate. -/
namespace BLS
open OracleComp OracleSpec

/-- Ordinary attacker families within polynomial component allowances have
negligible EUF-CMA success under Caliper co-CDH hardness. -/
theorem cocdh_security_asymptotic
    (curve : Model.PairingCurve) [model : CoCDHSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, UnrestrictedAdversary curve n (queries n))
    (resources : CaliperCoCDH.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : CaliperCoCDH.Family.coCDHHardness (fun n => model.parameters n (queries n))) :
    negligible (fun n => 𝒟[cocdhEufCmaGame curve n (adversary n)] {true}) :=
  CaliperCoCDH.Family.Proofs.security curve queries adversary resources hardness

end BLS
