import Signatures.Schnorr.GeneralNonzeroROMFamilyResources
import Signatures.Model.ForkingNegligible
import Signatures.Model.NonzeroFieldGrowth

/-! Negligible nonzero-nonce Schnorr ROM forgery from the derived native reduction
family. Polynomial queries absorb signing and fork losses; the square-root
consequence of the original forking bound also preserves negligibility. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM
open Signatures.Runtime.Schnorr.ListROM.NativeSolver.Family

namespace Schnorr.NonzeroNonce.GeneralROM.Family.Proofs

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]
  {F G M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, SampleableType (F n)ˣ] [∀ n, Fintype (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)] [∀ n, SampleableType (G n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]

theorem security
    (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G := G n) (M := M n))
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (adversary : ∀ n, UnrestrictedAdversary (parameters n))
    (hardness : dlogNonuniformHardness config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).inputWidth))
    (fieldGrowth : negligible (fun n => (Fintype.card (F n) : ENNReal)⁻¹)) :
    negligible (fun n => 𝒟[NonzeroNonce.game (parameters n).generator (adversary n).source] {true}) := by
  have fits := reduction_nonuniform parameters config fixed resources adversary
  have solverSmall := hardness _ fits
  have signingLossSmall : negligible (fun n =>
      ((parameters n).queries.sign : ENNReal) * ((parameters n).queries.sign + (parameters n).queries.hash) *
        ((Fintype.card (F n) - 1 : Nat) : ENNReal)⁻¹) := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      (resources.signingQueries.mul (resources.signingQueries.add resources.hashQueries)).negligible_mul
        (Model.negligible_inv_card_sub_one fieldGrowth)
  apply Model.negligible_of_forking_bound
    (fun n => MeasureTheory.measure_ne_top _ _)
    (fun n => ENNReal.inv_ne_top.mpr (by positivity)) resources.hashQueries
    signingLossSmall fieldGrowth solverSmall
  intro n
  rw [NonzeroListROM.NativeSolver.reduction_experiment (G₂ := G n) (K := M n)
    (parameters n).generator (adversary n).source (parameters n).queries.hash]
  exact NonzeroNonce.LazyROM.security (parameters n).generator (parameters n).generates (adversary n).source
    (parameters n).queries.sign (parameters n).queries.hash
    (fun pk => ⟨(adversary n).signingQueries pk, (adversary n).hashQueries pk⟩)

end Schnorr.NonzeroNonce.GeneralROM.Family.Proofs
