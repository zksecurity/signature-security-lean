import Signatures.BLS.CaliperAGMFamilyResources
import Proofs.BLS.GeneralSecurity

/-! Negligible BLS AGM forgery probability from the actual polynomial-resource
Caliper reduction families. The pointwise probability proof is unchanged. -/
namespace BLS.CaliperAGM.Family.Proofs
open OracleComp OracleSpec Signatures.Runtime

theorem security
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (queries : Nat → QueryAllowance)
    (adversary : ∀ n, BLS.AlgebraicAdversary curve n (queries n))
    (resources : PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    negligible (fun n => 𝒟[BLS.agmEufCmaGame curve n (adversary n)] {true}) := by
  let parameters := fun n => model.parameters n (queries n)
  obtain ⟨goodFits, badFits⟩ := reductions_nonuniform parameters resources adversary
  have goodSmall := hardness _ goodFits
  have badSmall := hardness _ badFits
  apply negligible_of_le _ (negligible_add (negligible_add goodSmall badSmall) fieldGrowth)
  intro n
  rw [BLS.agmEufCmaGame_eq]
  apply (Model.DirectAGM.game_le (Gₜ := curve.TargetGroup n) BLS.LazyAGM.terms (fun _ _ => True)
    (curve.generator n) (curve.keyGenerator n) (adversary n).source).trans
  simpa only [BLS.LazyAGM.game, Pi.add_apply, Model.PairingCurve.order, parameters, AlgebraicAdversary.proofView] using
    BLS.LazyAGM.Reduction.security_arbitrary_messages_list (Gₜ := curve.TargetGroup n)
      (curve.generator n) (curve.keyGenerator n) (adversary n).proofView
      (curve.generates n) (curve.pairingInjective n)

end BLS.CaliperAGM.Family.Proofs
