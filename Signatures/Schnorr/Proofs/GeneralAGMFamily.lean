import Signatures.Schnorr.GeneralAGMFamilyResources

/-! Negligible Schnorr AGM forgery from the actual native solver family.
Both original query-dependent losses are polynomial multiples of inverse field
size; no reduction efficiency premise is added to the security theorem. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native
open Signatures.Runtime.SchnorrAGM.Native.Solver.Family

namespace Schnorr.GeneralAGM.Family.Proofs

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, Fintype (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]
  [∀ n, DecidableEq (Interface.SourceRequest (F n) (G n) (M n))]

theorem security
    (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G := G n) (M := M n))
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n))
    (hardness : dlogNonuniformHardness config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).inputWidth))
    (fieldGrowth : negligible (fun n => (Fintype.card (F n) : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[AGM.game (parameters n).generator (adversary n).source] {true}) := by
  have fits := reduction_nonuniform parameters config fixed resources adversary
  have solverSmall := hardness _ fits
  have hashLossSmall : negligible (fun n =>
      ((parameters n).queries.hash + 1 : ENNReal) * (Fintype.card (F n) : ENNReal)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (resources.hashQueries.add (PolynomiallyBounded.const 1)).negligible_mul fieldGrowth
  have signingLossSmall : negligible (fun n =>
      ((parameters n).queries.sign : ENNReal) * ((parameters n).queries.sign + (parameters n).queries.hash) *
        (Fintype.card (F n) : ENNReal)⁻¹) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (resources.signingQueries.mul (resources.signingQueries.add resources.hashQueries)).negligible_mul fieldGrowth
  apply negligible_of_le _ (negligible_add (negligible_add solverSmall hashLossSmall) signingLossSmall)
  intro n
  exact SchnorrAGM.security (parameters n).generator (parameters n).generates.1 (adversary n).source
    (parameters n).queries.sign (parameters n).queries.hash (adversary n).signingQueries (adversary n).hashQueries

end Schnorr.GeneralAGM.Family.Proofs
