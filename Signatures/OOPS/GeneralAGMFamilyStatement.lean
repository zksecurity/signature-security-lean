import Signatures.OOPS.Proofs.GeneralAGMFamily

/-! OOPS family security for general implemented algebraic attackers in one fixed
backend. Polynomial degree and component bounds imply polynomial reduction time
and stored code. The original target-topic distinct-message rule is preserved. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram Signatures.Runtime.WeightedAGM
open Signatures.Runtime.WeightedAGM.NativeSolver.Family

namespace OOPS.GeneralAGM.Family

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
  [∀ n, AlgebraicGroupModel.BilinearPairing (F n) (G₁ n) (G₂ n) (Gₜ n)]
  {degree : Nat → Nat}
  (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G₁ := G₁ n) (G₂ := G₂ n)
    (Gₜ := Gₜ n) (K := K n) (M := M n) (degree n))
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

/-- Negligible forgery from fixed-backend hardness and the stated loss hypotheses. -/
theorem security_asymptotic :
    negligible (fun n => 𝒟[OOPS.LazyAGM.game (Gₜ := Gₜ n)
      (parameters n).generator (parameters n).keyGenerator (degree n) (adversary n).source] {true}) :=
  Proofs.security parameters config fixed resources adversary hardness fieldGrowth

end OOPS.GeneralAGM.Family
