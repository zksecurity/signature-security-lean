import Signatures.Proximity.Proofs.GeneralAGMFamily

/-! Family security for general implemented algebraic attackers in one fixed
backend. Polynomial component bounds imply polynomial reduction time and code.
For Proximity, the original collision probability is explicit. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM
open Signatures.Runtime.WeightedAGM.NativeSolver.Family

namespace Proximity.GeneralAGM.Family

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ K M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G₁ n)] [∀ n, DecidableEq (G₂ n)]
  [∀ n, DecidableEq (K n)] [∀ n, DecidableEq (M n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)]
  [∀ n, AddCommGroup (Gₜ n)] [∀ n, Module (F n) (Gₜ n)]
  [∀ n, BilinearGroup.BilinearPairing (F n) (G₁ n) (G₂ n) (Gₜ n)]
  {dimension : Nat → Nat}
  (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G₁ := G₁ n) (G₂ := G₂ n)
    (Gₜ := Gₜ n) (K := K n) (M := M n) (dimension n))
  (config : Configuration.{v, w, x} Q unifSpec)
  (fixed : ∀ n, (parameters n).configuration = config)
  (resources : General.Family.PolynomialResources parameters)
  (adversary : ∀ n, AlgebraicAdversary (parameters n))

variable [∀ n, Fintype (F n)] [∀ n, SampleableType (G₁ n)] [∀ n, Fintype (G₁ n)]
  [∀ n, DecidableEq (Gₜ n)]
  (hardness : dlogNonuniformHardness config (fun n => (parameters n).rep)
    (fun n => (parameters n).generator) (fun n => (parameters n).keyGenerator)
    (fun n => (parameters n).inputWidth))
  (fieldGrowth : negligible (fun n => 1 / (Fintype.card (F n) : ENNReal)))

include fixed resources hardness fieldGrowth

/-- The original collision probability plus a negligible error bounds forgery. -/
theorem security_up_to_collision :
    ∃ error : Nat → ENNReal, negligible error ∧ ∀ n,
      𝒟[Model.DirectAGM.game (Gₜ := Gₜ n) Proximity.LazyAGM.terms (fun _ _ => True)
      (parameters n).generator (parameters n).keyGenerator (adversary n).source] {true} ≤
        error n + 𝒟[Proximity.DirectAGM.collisionGame (parameters n).generator (parameters n).keyGenerator (adversary n).source] {true} :=
  Proofs.security_up_to_collision parameters config fixed resources adversary hardness fieldGrowth

/-- Negligible forgery from fixed-backend hardness and the stated loss hypotheses. -/
theorem security_asymptotic
    (collisionSmall : negligible (fun n => 𝒟[Proximity.DirectAGM.collisionGame (parameters n).generator (parameters n).keyGenerator (adversary n).source] {true})) :
    negligible (fun n => 𝒟[Model.DirectAGM.game (Gₜ := Gₜ n) Proximity.LazyAGM.terms (fun _ _ => True)
      (parameters n).generator (parameters n).keyGenerator (adversary n).source] {true}) :=
  Proofs.security parameters config fixed resources adversary hardness fieldGrowth collisionSmall

end Proximity.GeneralAGM.Family
