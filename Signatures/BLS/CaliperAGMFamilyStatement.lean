import Signatures.BLS.Proofs.CaliperAGMFamily

/-! Asymptotic security for the public BLS AGM Caliper model. Polynomial bounds
on the original component resources imply polynomial reductions. Their DLog
hardness and negligible inverse group order imply negligible forgery success.
This is nonuniform security in the fixed Caliper family and ideal uniform
sampling model; broader caller coverage and CPU adequacy remain separate. -/
namespace BLS
open OracleComp OracleSpec

/-- Every algebraic attacker family within the polynomial component allowances
has negligible EUF-CMA success under Caliper DLog hardness and sufficient group growth. -/
theorem agm_security_asymptotic
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, AlgebraicAdversary curve n (queries n))
    (resources : CaliperAGM.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : CaliperAGM.Family.dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    negligible (fun n => 𝒟[agmEufCmaGame curve n (adversary n)] {true}) :=
  CaliperAGM.Family.Proofs.security curve queries adversary resources hardness fieldGrowth

end BLS
