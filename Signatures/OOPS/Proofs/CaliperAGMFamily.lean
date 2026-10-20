import Signatures.Runtime.Caliper.WeightedFamilyResources
import Signatures.OOPS.Proofs.GeneralSecurity

/-! Asymptotic security from the complete weighted Caliper reductions.
Their code, time and total memory follow from polynomial local resources.
The source game and its probability losses are unchanged. -/
namespace OOPS.CaliperAGM.Family.Proofs
open OracleComp OracleSpec Signatures.Runtime

theorem security
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (degree : Nat → Nat) (queries : Nat → QueryAllowance)
    (adversary : ∀ n, OOPS.AlgebraicAdversary curve n (degree n) (queries n))
    (resources : WeightedCaliper.Family.PolynomialResources (fun n => model.parameters n (degree n) (queries n)))
    (hardness : WeightedCaliper.Family.dlogHardness (fun n => model.parameters n (degree n) (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    negligible (fun n => 𝒟[OOPS.agmEufCmaGame curve n (degree n) (adversary n)] {true}) := by
  let parameters := fun n => model.parameters n (degree n) (queries n)
  obtain ⟨goodFits, badFits⟩ := WeightedCaliper.Family.reductions_nonuniform parameters resources adversary
  have goodSmall := hardness _ goodFits
  have badSmall := hardness _ badFits
  apply negligible_of_le _ (negligible_add (negligible_add goodSmall badSmall) fieldGrowth)
  intro n
  rw [OOPS.agmEufCmaGame_eq]
  apply (Model.DirectAGM.game_le (Gₜ := curve.TargetGroup n) (LazyAGM.terms (degree n)) (LazyAGM.admissible (degree n))
    (curve.generator n) (curve.keyGenerator n) (adversary n).source).trans
  simpa only [OOPS.LazyAGM.game_eq_of_decidableEq, Pi.add_apply, Model.PairingCurve.order, parameters,
    WeightedCaliper.AlgebraicAdversary.proofView] using
    OOPS.LazyAGM.Proofs.security_arbitrary_topics (Gₜ := curve.TargetGroup n)
      (curve.generator n) (curve.keyGenerator n) (degree n) (adversary n).proofView
      (curve.generates n) (curve.pairingInjective n)

end OOPS.CaliperAGM.Family.Proofs
