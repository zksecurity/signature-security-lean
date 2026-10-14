import Signatures.BLS.Proofs.GeneralAGMFamily

/-! Asymptotic BLS AGM security for general realized attackers. The concrete
parameters select groups, encodings, query allowances and caller resources at
each security parameter. Polynomial component bounds and one fixed backend
yield polynomial reduction families; DLog hardness and negligible inverse
field size then give negligible forgery probability. The proof is separate. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.LazyAGM.NativeSolver.Family

namespace BLS.GeneralAGM.Family

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G₁ G₂ Gₜ M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, Fintype (F n)]
  [∀ n, SampleableType (G₁ n)] [∀ n, Fintype (G₁ n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G₁ n)] [∀ n, DecidableEq (G₂ n)]
  [∀ n, DecidableEq (Gₜ n)] [∀ n, DecidableEq (M n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)]
  [∀ n, AddCommGroup (Gₜ n)] [∀ n, Module (F n) (Gₜ n)]
  [∀ n, AlgebraicGroupModel.BilinearPairing (F n) (G₁ n) (G₂ n) (Gₜ n)]

/-- Polynomial-resource algebraic attackers have negligible forgery success
under nonuniform DLog hardness in the fixed backend and negligible `1 / |F|`.
There is no finite-message assumption or completed-solver efficiency premise. -/
theorem security_asymptotic
    (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G₁ := G₁ n) (G₂ := G₂ n) (Gₜ := Gₜ n) (M := M n))
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n))
    (hardness : dlogNonuniformHardness config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).keyGenerator)
      (fun n => (parameters n).inputWidth))
    (fieldGrowth : negligible (fun n => 1 / (Fintype.card (F n) : ENNReal))) :
    negligible (fun n => 𝒟[BLS.LazyAGM.game (Gₜ := Gₜ n)
      (parameters n).generator (parameters n).keyGenerator (adversary n).source] {true}) :=
  Proofs.security parameters config fixed resources adversary hardness fieldGrowth

end BLS.GeneralAGM.Family
