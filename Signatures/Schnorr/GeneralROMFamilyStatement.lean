import Proofs.Schnorr.GeneralROMFamily

/-! Ordinary-ROM Schnorr security for polynomial unrestricted attacker
families. One backend and cost/description convention is fixed across parameters.
The complete reduction's polynomial resources are derived, not assumed. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr.ListROM.NativeSolver.Family

namespace Schnorr.GeneralROM.Family

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, Fintype (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)] [∀ n, SampleableType (G n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]

/-- Under nonuniform DLog hardness and negligible inverse field size, every
unrestricted attacker family within polynomial original resources has negligible
EUF-CMA success. Curve/group/message types may vary with the security parameter. -/
theorem security_asymptotic
    (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G := G n) (M := M n))
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (adversary : ∀ n, UnrestrictedAdversary (parameters n))
    (hardness : dlogNonuniformHardness config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).inputWidth))
    (fieldGrowth : negligible (fun n => (Fintype.card (F n) : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[ROM.game (parameters n).generator (adversary n).source] {true}) :=
  Proofs.security parameters config fixed resources adversary hardness fieldGrowth

end Schnorr.GeneralROM.Family
