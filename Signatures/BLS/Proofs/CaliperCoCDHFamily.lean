import Signatures.BLS.CaliperCoCDHFamilyResources
import Signatures.BLS.Proofs.GeneralSecurity
import Signatures.Model.CoronLoss

/-! Negligible co-CDH advantage and polynomial component bounds imply
negligible BLS forgery probability for the actual Caliper reduction family. -/
namespace BLS.CaliperCoCDH.Family.Proofs
open OracleComp OracleSpec Signatures.Runtime

theorem security (curve : Model.PairingCurve) [model : CoCDHSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, BLS.UnrestrictedAdversary curve n (queries n))
    (resources : PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : coCDHHardness (fun n => model.parameters n (queries n))) :
    negligible (fun n => 𝒟[BLS.cocdhEufCmaGame curve n (adversary n)] {true}) := by
  have fits := reduction_nonuniform (fun n => model.parameters n (queries n)) resources adversary
    (fun n => (curve.generates n).surjective)
  have small := hardness _ fits
  exact Model.negligible_of_coron_bound resources.signingQueries small
    (fun n => BLS.Proofs.cocdh_probability curve n (queries n) (adversary n))

end BLS.CaliperCoCDH.Family.Proofs
