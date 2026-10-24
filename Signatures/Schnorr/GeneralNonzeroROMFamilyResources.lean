import Proofs.Schnorr.GeneralNonzeroROM
import Proofs.Runtime.BackendSchnorrNonzeroSolverPolynomial
import Proofs.Runtime.BackendSchnorrNonzeroDescriptionPolynomial
import Signatures.Runtime.BackendSchnorrROMDLogFamily

/-! Polynomial resources for unrestricted nonzero-nonce Schnorr ROM attackers in one fixed
backend. Complete solver time/code and family membership follow from original
resources and the actual native pointwise implementation certificate. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.Schnorr ListROM
open Signatures.Runtime.Schnorr.ListROM.NativeSolver.Family

namespace Schnorr.NonzeroNonce.GeneralROM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]

def Parameters.configuration {F G M : Type} [Field F] [SampleableType F] [SampleableType Fˣ]
    [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    (P : Parameters (Q := Q) (F := F) (G := G) (M := M)) : Configuration.{v, w, x} Q unifSpec :=
  ⟨P.iface, P.control, P.queryCost, P.backend, P.descriptionSizes, P.factor, P.description⟩

namespace Family

variable {F G M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, SampleableType (F n)ˣ]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]
  (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G := G n) (M := M n))

/-- Fixed polynomial bounds for original caller work, queries, widths, sampler
profiles, primitive/port prices and stored descriptions. No completed solver
resource appears as a premise. Numeric random arity and domain size are absent. -/
structure PolynomialResources : Prop where
  overhead : PolynomialOverhead (fun n => (parameters n).overhead)
  work : PolynomiallyBounded (fun n => (parameters n).execution.work)
  randomQueries : PolynomiallyBounded (fun n => (parameters n).queries.random)
  hashQueries : PolynomiallyBounded (fun n => (parameters n).queries.hash)
  signingQueries : PolynomiallyBounded (fun n => (parameters n).queries.sign)
  inputWidth : PolynomiallyBounded (fun n => (parameters n).inputWidth)
  width : PolynomiallyBounded (fun n => (parameters n).width)
  tapeWidth : PolynomiallyBounded (fun n => (parameters n).tapeWidth)
  first : NonzeroListROM.NativePass.TimeInputs.Polynomial (fun n => (parameters n).first.timeInputs)
  second : NonzeroListROM.NativePass.TimeInputs.Polynomial (fun n => (parameters n).second.timeInputs)
  scaleTime : PolynomiallyBounded (fun n => (parameters n).scaleTime)
  addTime : PolynomiallyBounded (fun n => (parameters n).addTime)
  messageTime : PolynomiallyBounded (fun n => (parameters n).messageTime)
  pointTime : PolynomiallyBounded (fun n => (parameters n).pointTime)
  incrementTime : PolynomiallyBounded (fun n => (parameters n).incrementTime)
  comparisonTime : PolynomiallyBounded (fun n => (parameters n).comparisonTime)
  scalarComparisonTime : PolynomiallyBounded (fun n => (parameters n).scalarComparisonTime)
  subtractTime : PolynomiallyBounded (fun n => (parameters n).subtractTime)
  extractionScalarTime : PolynomiallyBounded (fun n => (parameters n).extractionScalarTime)
  fieldSubTime : PolynomiallyBounded (fun n => (parameters n).fieldSubTime)
  divTime : PolynomiallyBounded (fun n => (parameters n).divTime)
  descriptions : NonzeroListROM.NativeSolver.DescriptionInputs.Polynomial (fun n => (parameters n).descriptions)
  allowance : PolynomiallyBounded (fun n => (parameters n).allowance)

namespace PolynomialResources

variable {parameters} (resources : PolynomialResources parameters)

include resources

theorem totalQueries : PolynomiallyBounded (fun n => (parameters n).queries.total) :=
  (resources.randomQueries.add resources.hashQueries).add resources.signingQueries

theorem executionQueries : PolynomiallyBounded (fun n => (parameters n).execution.queries) :=
  resources.totalQueries.of_le (fun n => (parameters n).queryCapacity)

theorem solverTime : PolynomiallyBounded (fun n => (parameters n).solverTime) :=
  NonzeroListROM.NativeSolver.resourcesTime_polynomial (fun n => (parameters n).overhead) (fun n => (parameters n).execution)
    (fun n => (parameters n).width) (fun n => (parameters n).tapeWidth)
    (fun n => (parameters n).queries.total) (fun n => (parameters n).queries.total) (fun n => (parameters n).queries.total)
    (fun n => (parameters n).first.timeInputs) (fun n => (parameters n).second.timeInputs)
    (fun n => (parameters n).scaleTime) (fun n => (parameters n).addTime) (fun n => (parameters n).messageTime)
    (fun n => (parameters n).pointTime) (fun n => (parameters n).incrementTime) (fun n => (parameters n).comparisonTime)
    (fun n => (parameters n).scalarComparisonTime) (fun n => (parameters n).subtractTime)
    (fun n => (parameters n).extractionScalarTime) (fun n => (parameters n).fieldSubTime) (fun n => (parameters n).divTime)
    resources.first resources.second resources.overhead resources.work resources.executionQueries
    resources.width resources.tapeWidth resources.totalQueries resources.totalQueries resources.totalQueries
    resources.scaleTime resources.addTime resources.messageTime resources.pointTime resources.incrementTime
    resources.comparisonTime resources.scalarComparisonTime resources.subtractTime resources.extractionScalarTime
    resources.fieldSubTime resources.divTime

theorem solverCode (hFactor : PolynomiallyBounded (fun n => (parameters n).factor)) :
    PolynomiallyBounded (fun n => (parameters n).solverCode) :=
  NonzeroListROM.NativeSolver.DescriptionInputs.compiled_polynomial (fun n => (parameters n).descriptions)
    (fun n => (parameters n).factor) (fun n => (parameters n).allowance)
    (fun n => (parameters n).queries.total) (fun n => (parameters n).queries.hash)
    resources.descriptions hFactor resources.allowance resources.totalQueries resources.hashQueries

end PolynomialResources

variable [∀ n, SampleableType (G n)]

/-- The actual unrestricted reduction family belongs to the common polynomial
time/code class, with every challenge covered by its input-size bound. -/
theorem reduction_nonuniform
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (adversary : ∀ n, UnrestrictedAdversary (parameters n)) :
    dlogNonuniformWithin config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).inputWidth)
      (fun n => NonzeroListROM.NativeSolver.reduction (G₂ := G n) (K := M n) (adversary n).source.main (parameters n).queries.hash) := by
  have certificates := fun n => reduction_within (parameters n) (adversary n)
  have hFactor : PolynomiallyBounded (fun n => (parameters n).factor) :=
    (PolynomiallyBounded.const config.factor).of_le (fun n =>
      le_of_eq (congrArg Configuration.factor (fixed n)))
  refine ⟨fun n => (certificates n).1, ?_⟩
  apply config.nonuniformWithin_of_pointwise _ _ _
    (fun n => (parameters n).solverCode) (fun n => (parameters n).solverTime) _
    resources.inputWidth (resources.solverCode hFactor) resources.solverTime
  intro n
  have h := (certificates n).2
  change ((parameters n).configuration).within _ _ _ _ _ _ at h
  rw [fixed n] at h
  exact h

end Family

end Schnorr.NonzeroNonce.GeneralROM
