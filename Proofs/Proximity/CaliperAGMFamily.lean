import Proofs.Runtime.Caliper.WeightedFamilyResources
import Proofs.Proximity.GeneralSecurity

/-! Asymptotic security from the complete weighted Caliper reductions.
Their code, time and total memory follow from polynomial local resources.
The source game and its probability losses are unchanged. -/
namespace Proximity.CaliperAGM.Family.Proofs
open OracleComp OracleSpec Signatures.Runtime

theorem security_up_to_collision
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (dimension : Nat → Nat) (queries : Nat → QueryAllowance)
    (adversary : ∀ n, Proximity.AlgebraicAdversary curve n (dimension n) (queries n))
    (resources : WeightedCaliper.Family.PolynomialResources (fun n => model.parameters n (dimension n) (queries n)))
    (hardness : WeightedCaliper.Family.dlogHardness (fun n => model.parameters n (dimension n) (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    ∃ error : Nat → ENNReal, negligible error ∧ ∀ n,
      𝒟[Proximity.agmEufCmaGame curve n (dimension n) (adversary n)] {true} ≤ error n + 𝒟[Proximity.freshCollisionGame curve n (dimension n) (adversary n)] {true} := by
  let parameters := fun n => model.parameters n (dimension n) (queries n)
  obtain ⟨goodFits, badFits⟩ := WeightedCaliper.Family.reductions_nonuniform parameters resources adversary
  have goodSmall := hardness _ goodFits
  have badSmall := hardness _ badFits
  refine ⟨_, negligible_add (negligible_add goodSmall badSmall) fieldGrowth, ?_⟩
  intro n
  rw [Proximity.agmEufCmaGame_eq, Proximity.freshCollisionGame_eq]
  apply (Model.DirectAGM.game_le (Gₜ := curve.TargetGroup n) (LazyAGM.terms) (fun _ _ => True)
    (curve.generator n) (curve.keyGenerator n) (adversary n).source).trans
  simpa only [LazyAGM.game, Pi.add_apply, Model.PairingCurve.order, parameters,
    WeightedCaliper.AlgebraicAdversary.proofView] using
    Proximity.LazyAGM.Proofs.security_arbitrary_slots (Gₜ := curve.TargetGroup n)
      (curve.generator n) (curve.keyGenerator n) (adversary n).proofView
      (curve.generates n) (curve.pairingInjective n)

/-- The collision term needs its own assumption; DLog hardness alone does not remove it. -/
theorem security
    (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (dimension : Nat → Nat) (queries : Nat → QueryAllowance)
    (adversary : ∀ n, Proximity.AlgebraicAdversary curve n (dimension n) (queries n))
    (resources : WeightedCaliper.Family.PolynomialResources (fun n => model.parameters n (dimension n) (queries n)))
    (hardness : WeightedCaliper.Family.dlogHardness (fun n => model.parameters n (dimension n) (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal)))
    (collisionSmall : negligible (fun n => 𝒟[Proximity.freshCollisionGame curve n (dimension n) (adversary n)] {true})) :
    negligible (fun n => 𝒟[Proximity.agmEufCmaGame curve n (dimension n) (adversary n)] {true}) := by
  obtain ⟨error, errorSmall, bound⟩ := security_up_to_collision
    curve dimension queries adversary resources hardness fieldGrowth
  exact negligible_of_le bound (negligible_add errorSmall collisionSmall)

end Proximity.CaliperAGM.Family.Proofs
