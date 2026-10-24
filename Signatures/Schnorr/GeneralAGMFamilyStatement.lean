import Proofs.Schnorr.GeneralAGMFamily

/-! Asymptotic Schnorr AGM security for general realized attackers in one
fixed backend. The actual reduction's polynomial time and stored-code bounds
are derived from component resources. DLog hardness and negligible inverse
field size then make forgery negligible, preserving both original query losses. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native
open Signatures.Runtime.SchnorrAGM.Native.Solver.Family

namespace Schnorr.GeneralAGM.Family

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, Fintype (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]
  [∀ n, DecidableEq (Interface.SourceRequest (F n) (G n) (M n))]

/-- Polynomial-resource algebraic attackers have negligible forgery success
under nonuniform DLog hardness and negligible inverse field size. The backend
and cost convention are fixed across the family; messages may be arbitrary. -/
theorem security_asymptotic
    (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G := G n) (M := M n))
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n))
    (hardness : dlogNonuniformHardness config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).inputWidth))
    (fieldGrowth : negligible (fun n => (Fintype.card (F n) : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[AGM.game (parameters n).generator (adversary n).source] {true}) :=
  Proofs.security parameters config fixed resources adversary hardness fieldGrowth

end Schnorr.GeneralAGM.Family
