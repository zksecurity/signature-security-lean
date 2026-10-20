import Signatures.OOPS.Proofs.CaliperAGMFamily

/-! Public nonuniform security in the fixed Caliper family. Only local resource
growth is assumed; complete reduction resources are derived. Conventional CPU
adequacy and broader caller coverage remain separate. -/
namespace OOPS
open OracleComp OracleSpec Signatures.Runtime

/-- Polynomial component allowances and Caliper DLog hardness imply negligible forgery success
when the inverse field size is negligible. -/
theorem agm_security_asymptotic
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (degree : Nat → Nat) (queries : Nat → QueryAllowance)
    (adversary : ∀ n, OOPS.AlgebraicAdversary curve n (degree n) (queries n))
    (resources : WeightedCaliper.Family.PolynomialResources (fun n => model.parameters n (degree n) (queries n)))
    (hardness : WeightedCaliper.Family.dlogHardness (fun n => model.parameters n (degree n) (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    negligible (fun n => 𝒟[OOPS.agmEufCmaGame curve n (degree n) (adversary n)] {true}) :=
  CaliperAGM.Family.Proofs.security
    curve degree queries adversary resources hardness fieldGrowth

end OOPS
