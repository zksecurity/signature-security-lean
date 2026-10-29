import Proofs.SynchronizedPS.GeneralAGMFamily

/-! Public nonuniform synchronized PS security for general implemented algebraic attackers in one
fixed backend. Polynomial component bounds imply polynomial reduction time and stored code at every
known key; the game stays the public algebraic experiment at the curve. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM
open Signatures.Runtime.WeightedAGM.NativeSolver.Family

namespace SynchronizedPS.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]

/-- Polynomial component allowances and fixed-backend DLog hardness imply negligible forgery
success at the curve when the inverse field size is negligible. -/
theorem agm_security_asymptotic (curve : Model.PairingCurve) {K M : Nat → Type}
    [∀ n, DecidableEq (K n)] [∀ n, DecidableEq (M n)]
    (parameters : ∀ n, Parameters (Q := Q) (F := curve.Scalar n) (G₁ := curve.SignatureGroup n)
      (G₂ := curve.KeyGroup n) (Gₜ := curve.TargetGroup n) (K := K n) (M := M n)
      (curve.generator n) (curve.keyGenerator n))
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : Family.Fixed parameters config)
    (resources : Family.PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n))
    (hardness : Family.dlogHardness parameters config)
    (fieldGrowth : negligible (fun n => 1 / (curve.order n : ENNReal))) :
    negligible (fun n => 𝒟[Game.agm curve n (adversary n).source] {true}) := by
  apply negligible_of_le _ (Family.Proofs.security parameters config fixed resources adversary hardness fieldGrowth)
  intro n
  exact Game.agm_le curve n (adversary n).source

end SynchronizedPS.GeneralAGM
