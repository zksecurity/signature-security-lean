import Proofs.Runtime.Caliper.SyncWrapFamilyResources
import Proofs.SynchronizedPS.CaliperSecurity

/-! Asymptotic synchronized PS security from the four complete Caliper solvers. Their code,
time and total memory follow from polynomial local resources; the source game and its
probability losses are unchanged. -/
namespace SynchronizedPS.CaliperAGM.Family.Proofs
open OracleComp OracleSpec Signatures.Runtime

theorem security (curve : Model.PairingCurve) [model : AGMSecurityModel curve]
    (queries : Nat → QueryAllowance) (adversary : ∀ n, SynchronizedPS.AlgebraicAdversary curve n (queries n))
    (resources : SyncWrapCaliper.Family.PolynomialResources (fun n => model.parameters n (queries n)))
    (hardness : SyncWrapCaliper.Family.dlogHardness (fun n => model.parameters n (queries n)))
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    negligible (fun n => 𝒟[SynchronizedPS.agmEufCmaGame curve n (adversary n)] {true}) := by
  let parameters := fun n => model.parameters n (queries n)
  obtain ⟨good₁, bad₁, good₂, bad₂⟩ := SyncWrapCaliper.Family.reductions_nonuniform parameters resources adversary
  have small₁ := hardness _ good₁
  have small₂ := hardness _ bad₁
  have small₃ := hardness _ good₂
  have small₄ := hardness _ bad₂
  apply negligible_of_le _ (negligible_add (negligible_add (negligible_add (negligible_add small₁ small₂) small₃) small₄)
    (negligible_add fieldGrowth fieldGrowth))
  intro n
  have two : (2 : ENNReal) / (Fintype.card (curve.Scalar n) : ENNReal) =
      1 / (curve.order n : ENNReal) + 1 / (curve.order n : ENNReal) := by
    rw [Model.PairingCurve.order, ENNReal.div_add_div_same, one_add_one_eq_two]
  have bound := (Game.agm_le curve n (adversary n).source).trans
    (Transport.security_wrapped (Gₜ := curve.TargetGroup n) (SynchronizedPS.Proofs.view (adversary n).source (curve.generator n))
      (curve.generator n) (curve.keyGenerator n) (curve.generates n) (curve.pairingInjective n))
  rw [(adversary n).good₁_eq, (adversary n).bad₁_eq, (adversary n).good₂_eq, (adversary n).bad₂_eq, two] at bound
  simpa only [Pi.add_apply, SynchronizedPS.agmEufCmaGame, parameters] using bound

end SynchronizedPS.CaliperAGM.Family.Proofs
