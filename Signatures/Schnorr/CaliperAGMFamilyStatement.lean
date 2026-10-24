import Proofs.Schnorr.CaliperAGMFamily

/-! Asymptotic security for the public Schnorr AGM Caliper model. Polynomial
component allowances give polynomial reductions. DLog hardness and negligible
inverse group order then give negligible forgery success. -/
namespace Schnorr
open OracleComp OracleSpec

/-- Algebraic attacker families within polynomial Caliper allowances have
negligible EUF-CMA success under DLog hardness and sufficient group growth. -/
theorem agm_security_asymptotic
    (curve : Model.CyclicCurve) [model : AGMSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, AlgebraicAdversary curve n (queries n))
    (resources : CaliperAGM.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : CaliperAGM.Family.dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => (curve.order n : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[agmEufCmaGame curve n (adversary n)] {true}) :=
  CaliperAGM.Family.Proofs.security curve queries adversary resources hardness fieldGrowth

end Schnorr
