import Signatures.Schnorr.CaliperAGMFamilyResources
import Signatures.Schnorr.Proofs.GeneralSecurity

/-! Negligible Schnorr AGM forgery follows from the constructed polynomial
Caliper reduction and the original two query-dependent collision terms. -/
namespace Schnorr.CaliperAGM.Family.Proofs
open OracleComp OracleSpec Signatures.Runtime

theorem security
    (curve : Model.CyclicCurve) [model : AGMSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, Schnorr.AlgebraicAdversary curve n (queries n))
    (resources : PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => (curve.order n : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[Schnorr.agmEufCmaGame curve n (adversary n)] {true}) := by
  have fits := reduction_nonuniform (fun n => model.parameters n (queries n)) resources adversary
  have solverSmall := hardness _ fits
  have hashLossSmall : negligible (fun n => ((queries n).hash + 1 : ENNReal) * (curve.order n : ENNReal)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (resources.hashQueries.add (PolynomiallyBounded.const 1)).negligible_mul fieldGrowth
  have signingLossSmall : negligible (fun n =>
      ((queries n).sign : ENNReal) * ((queries n).sign + (queries n).hash) * (curve.order n : ENNReal)⁻¹) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (resources.signingQueries.mul (resources.signingQueries.add resources.hashQueries)).negligible_mul fieldGrowth
  apply negligible_of_le _ (negligible_add (negligible_add solverSmall hashLossSmall) signingLossSmall)
  intro n
  rw [Schnorr.agmEufCmaGame_eq]
  exact Signatures.Runtime.SchnorrAGM.security (curve.generator n) (curve.generates n).1 (adversary n).source
    (queries n).sign (queries n).hash (adversary n).signingQueries (adversary n).hashQueries

end Schnorr.CaliperAGM.Family.Proofs
