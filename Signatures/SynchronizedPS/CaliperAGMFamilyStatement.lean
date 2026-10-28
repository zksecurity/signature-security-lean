import Proofs.SynchronizedPS.CaliperAGMFamily

/-! Public nonuniform synchronized PS security in the fixed Caliper family. Only local resource
growth is assumed; complete reduction resources are derived. -/
namespace SynchronizedPS
open OracleComp OracleSpec Signatures.Runtime

/-- Polynomial component allowances and Caliper DLog hardness imply negligible forgery success
when the inverse field size is negligible. -/
theorem agm_security_asymptotic
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, AlgebraicAdversary curve n (queries n))
    (resources : SyncWrapCaliper.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : SyncWrapCaliper.Family.dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    negligible (fun n => 𝒟[agmEufCmaGame curve n (adversary n)] {true}) :=
  CaliperAGM.Family.Proofs.security curve queries adversary resources hardness fieldGrowth

end SynchronizedPS
