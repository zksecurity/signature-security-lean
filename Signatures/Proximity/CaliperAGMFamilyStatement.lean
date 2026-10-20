import Signatures.Proximity.Proofs.CaliperAGMFamily

/-! Public nonuniform security in the fixed Caliper family. Only local resource
growth is assumed; complete reduction resources are derived. Conventional CPU
adequacy and broader caller coverage remain separate. -/
namespace Proximity
open OracleComp OracleSpec Signatures.Runtime

/-- Forgery success is bounded by the original collision probability plus a negligible error. -/
theorem agm_security_asymptotic_up_to_collision
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (dimension : Nat → Nat) (queries : Nat → QueryAllowance)
    (adversary : ∀ n, Proximity.AlgebraicAdversary curve n (dimension n) (queries n))
    (resources : WeightedCaliper.Family.PolynomialResources (fun n => model.parameters n (dimension n) (queries n)))
    (hardness : WeightedCaliper.Family.dlogHardness (fun n => model.parameters n (dimension n) (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    ∃ error : Nat → ENNReal, negligible error ∧ ∀ n,
      𝒟[Proximity.agmEufCmaGame curve n (dimension n) (adversary n)] {true} ≤ error n + 𝒟[Proximity.freshCollisionGame curve n (dimension n) (adversary n)] {true} :=
  CaliperAGM.Family.Proofs.security_up_to_collision
    curve dimension queries adversary resources hardness fieldGrowth

/-- Polynomial component allowances and Caliper DLog hardness imply negligible forgery success
provided the original fresh-collision probability is also negligible. -/
theorem agm_security_asymptotic
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (dimension : Nat → Nat) (queries : Nat → QueryAllowance)
    (adversary : ∀ n, Proximity.AlgebraicAdversary curve n (dimension n) (queries n))
    (resources : WeightedCaliper.Family.PolynomialResources (fun n => model.parameters n (dimension n) (queries n)))
    (hardness : WeightedCaliper.Family.dlogHardness (fun n => model.parameters n (dimension n) (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal)))
    (collisionSmall : negligible (fun n => 𝒟[Proximity.freshCollisionGame curve n (dimension n) (adversary n)] {true})) :
    negligible (fun n => 𝒟[Proximity.agmEufCmaGame curve n (dimension n) (adversary n)] {true}) :=
  CaliperAGM.Family.Proofs.security
    curve dimension queries adversary resources hardness fieldGrowth collisionSmall

end Proximity
