import Signatures.Schnorr.CaliperROMFamilyResources
import Signatures.Schnorr.Proofs.GeneralROMSecurity
import Signatures.Model.ForkingNegligible

/-! Negligible ordinary-ROM Schnorr forgery from the constructed polynomial
Caliper reduction family. Polynomial queries absorb the signing and fork losses;
the square-root consequence of the forking bound preserves negligibility. -/
namespace Schnorr.CaliperROM.Family.Proofs
open OracleComp OracleSpec Signatures.Runtime

theorem security
    (curve : Model.CyclicCurve) [model : ROMSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, Schnorr.UnrestrictedAdversary curve n (queries n))
    (resources : PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => (curve.order n : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[Schnorr.romEufCmaGame curve n (adversary n)] {true}) := by
  have fits := reduction_nonuniform (fun n => model.parameters n (queries n)) resources adversary
    (fun n => model.sampling n (queries n)) (fun n => model.fullField n (queries n))
  have solverSmall := hardness _ fits
  have signingLossSmall : negligible (fun n =>
      ((queries n).sign : ENNReal) * ((queries n).sign + (queries n).hash) * (curve.order n : ENNReal)⁻¹) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (resources.signingQueries.mul (resources.signingQueries.add resources.hashQueries)).negligible_mul fieldGrowth
  apply Model.negligible_of_forking_bound
    (fun n => MeasureTheory.measure_ne_top _ _)
    (fun n => ENNReal.inv_ne_top.mpr (by unfold Model.CyclicCurve.order; positivity)) resources.hashQueries
    signingLossSmall fieldGrowth solverSmall
  intro n
  rw [Schnorr.romEufCmaGame_eq, Schnorr.ListROM.NativeSolver.reduction_experiment (G₂ := curve.Group n) (K := model.Message n)
    (curve.generator n) (adversary n).source (queries n).hash]
  exact LazyROM.security (curve.generator n) (curve.generates n) (adversary n).source (queries n).sign (queries n).hash
    (fun pk => ⟨(adversary n).signingQueries pk, (adversary n).hashQueries pk⟩)

end Schnorr.CaliperROM.Family.Proofs
