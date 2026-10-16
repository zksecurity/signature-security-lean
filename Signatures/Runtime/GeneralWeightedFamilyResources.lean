import Signatures.Runtime.GeneralWeightedCertificates
import Signatures.Runtime.BackendWeightedPolynomial
import Signatures.Runtime.BackendWeightedDLogFamily

/-! Polynomial resources and fixed-backend composition for weighted AGM families.
Only the attacker's resources and primitive/encoding bounds are assumed
polynomial. Both completed solver families are derived from the pointwise
certificates, including their stored code and every generated challenge. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.WeightedAGM.NativeSolver
open Signatures.Runtime.WeightedAGM.NativeSolver.Family

namespace Signatures.Runtime.WeightedAGM.General

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]

/-- Exactly the execution and description convention in the concrete parameters.
Requiring this configuration to be constant across parameters fixes the backend;
it is not a solver-cost premise. -/
def Parameters.configuration {F G₁ G₂ Gₜ K M : Type} [Field F] [SampleableType F]
    [DecidableEq F] [DecidableEq G₁] [DecidableEq G₂] [DecidableEq K] [DecidableEq M]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup Gₜ] [Module F Gₜ] [BilinearGroup.BilinearPairing F G₁ G₂ Gₜ]
    {index : Index}
    (P : Parameters (Q := Q) (F := F) (G₁ := G₁) (G₂ := G₂) (Gₜ := Gₜ) (K := K) (M := M) index) :
    Configuration.{v, w, x} Q unifSpec :=
  ⟨P.iface, P.control, P.queryCost, P.backend, P.descriptionSizes, P.factor, P.description⟩

namespace Family

variable {F G₁ G₂ Gₜ K M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G₁ n)] [∀ n, DecidableEq (G₂ n)]
  [∀ n, DecidableEq (K n)] [∀ n, DecidableEq (M n)]
  [∀ n, AddCommGroup (G₁ n)] [∀ n, Module (F n) (G₁ n)]
  [∀ n, AddCommGroup (G₂ n)] [∀ n, Module (F n) (G₂ n)]
  [∀ n, AddCommGroup (Gₜ n)] [∀ n, Module (F n) (Gₜ n)]
  [∀ n, BilinearGroup.BilinearPairing (F n) (G₁ n) (G₂ n) (Gₜ n)]
  {index : Nat → Index}
  (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G₁ := G₁ n) (G₂ := G₂ n) (Gₜ := Gₜ n) (K := K n) (M := M n) (index n))

/-- One fixed polynomial for each caller, encoding or primitive allowance.
The complete solver times and descriptions are conclusions of the lemmas below,
not fields of this contract. Neither message cardinality nor numerical field
cardinality is required to be polynomial. -/
structure PolynomialResources : Prop where
  degree : PolynomiallyBounded (fun n => (index n).bound)
  overhead : PolynomialOverhead (fun n => (parameters n).overhead)
  work : PolynomiallyBounded (fun n => (parameters n).execution.work)
  randomQueries : PolynomiallyBounded (fun n => (parameters n).queries.random)
  hashQueries : PolynomiallyBounded (fun n => (parameters n).queries.hash)
  signingQueries : PolynomiallyBounded (fun n => (parameters n).queries.sign)
  inputWidth : PolynomiallyBounded (fun n => (parameters n).inputWidth)
  width : PolynomiallyBounded (fun n => (parameters n).width)
  outputWidth : PolynomiallyBounded (fun n => (parameters n).outputWidth)
  routeWidth : PolynomiallyBounded (fun n => (parameters n).routeWidth)
  comparisonTime : PolynomiallyBounded (fun n => (parameters n).comparisonTime)
  scalarTime : PolynomiallyBounded (fun n => (parameters n).scalarTime)
  opTime : PolynomiallyBounded (fun n => (parameters n).opTime)
  handlerAdapterTime : PolynomiallyBounded (fun n => (parameters n).handlerAdapterTime)
  solverAdapterTime : PolynomiallyBounded (fun n => (parameters n).solverAdapterTime)
  dynamicTime : PolynomiallyBounded (fun n => (parameters n).dynamicTime)
  handlerTickTime : PolynomiallyBounded (fun n => (parameters n).handlerTickTime)
  callerTickTime : PolynomiallyBounded (fun n => (parameters n).callerTickTime)
  extractionTickTime : PolynomiallyBounded (fun n => (parameters n).extractionTickTime)
  callerCode : PolynomiallyBounded (fun n => (parameters n).callerCodeLimit)
  scalarCode : PolynomiallyBounded (fun n => (parameters n).sampling.scalar.descriptionSize (parameters n).descriptionSizes)
  dynamicCode : PolynomiallyBounded (fun n => (parameters n).sampler.code.descriptionSize (parameters n).descriptionSizes)
  structuralCode : PolynomiallyBounded (fun n => (parameters n).allowance)
  instructionCode : PolynomiallyBounded (fun n => (parameters n).instructionSize)
  handlerCode : PolynomiallyBounded (fun n => (parameters n).handlerPortSize)
  solverPortCode : PolynomiallyBounded (fun n => (parameters n).solverPortSize)

namespace PolynomialResources

variable {parameters} (resources : PolynomialResources parameters)

include resources

theorem totalQueries : PolynomiallyBounded (fun n => (parameters n).queries.total) :=
  (resources.randomQueries.add resources.hashQueries).add resources.signingQueries

theorem executionQueries : PolynomiallyBounded (fun n => (parameters n).execution.queries) :=
  resources.totalQueries.of_le (fun n => (parameters n).queryCapacity)

theorem goodTime : PolynomiallyBounded (fun n => (parameters n).goodTime) := by
  exact goodProgramTime_polynomial index (fun n => (parameters n).overhead) (fun n => (parameters n).execution)
    (fun n => (parameters n).inputWidth) (fun n => (parameters n).width)
    (fun n => (parameters n).outputWidth) (fun n => (parameters n).routeWidth)
    (fun n => (parameters n).queries.total) (fun n => (parameters n).queries.total)
    (fun n => (parameters n).comparisonTime) (fun n => (parameters n).scalarTime)
    (fun n => (parameters n).opTime) (fun n => (parameters n).handlerAdapterTime)
    (fun n => (parameters n).solverAdapterTime) (fun n => (parameters n).dynamicTime)
    (fun n => (parameters n).handlerTickTime) (fun n => (parameters n).callerTickTime) (fun n => (parameters n).extractionTickTime)
    resources.degree resources.overhead resources.work resources.executionQueries resources.inputWidth resources.width
    resources.outputWidth resources.routeWidth resources.totalQueries resources.totalQueries
    resources.comparisonTime resources.scalarTime resources.opTime resources.handlerAdapterTime
    resources.solverAdapterTime resources.dynamicTime resources.handlerTickTime resources.callerTickTime resources.extractionTickTime

theorem badTime : PolynomiallyBounded (fun n => (parameters n).badTime) := by
  exact badProgramTime_polynomial index (fun n => (parameters n).overhead) (fun n => (parameters n).execution)
    (fun n => (parameters n).inputWidth) (fun n => (parameters n).width)
    (fun n => (parameters n).outputWidth) (fun n => (parameters n).routeWidth)
    (fun n => (parameters n).queries.total) (fun n => (parameters n).queries.total)
    (fun n => (parameters n).comparisonTime) (fun n => (parameters n).scalarTime)
    (fun n => (parameters n).opTime) (fun n => (parameters n).handlerAdapterTime)
    (fun n => (parameters n).solverAdapterTime) (fun n => (parameters n).dynamicTime)
    (fun n => (parameters n).handlerTickTime) (fun n => (parameters n).callerTickTime) (fun n => (parameters n).extractionTickTime)
    resources.degree resources.overhead resources.work resources.executionQueries resources.inputWidth resources.width
    resources.outputWidth resources.routeWidth resources.totalQueries resources.totalQueries
    resources.comparisonTime resources.scalarTime resources.opTime resources.handlerAdapterTime
    resources.solverAdapterTime resources.dynamicTime resources.handlerTickTime resources.callerTickTime resources.extractionTickTime

theorem solverCode (hFactor : PolynomiallyBounded (fun n => (parameters n).factor)) :
    PolynomiallyBounded (fun n => (parameters n).solverCode) := by
  exact programDescription_polynomial (fun n => (parameters n).factor) (fun n => (index n).bound)
    (fun n => (parameters n).callerCodeLimit)
    (fun n => (parameters n).sampling.scalar.descriptionSize (parameters n).descriptionSizes)
    (fun n => (parameters n).sampler.code.descriptionSize (parameters n).descriptionSizes)
    (fun n => (parameters n).queries.total) (fun n => (parameters n).allowance)
    (fun n => (parameters n).instructionSize) (fun n => (parameters n).handlerPortSize)
    (fun n => (parameters n).solverPortSize) hFactor resources.degree resources.callerCode resources.scalarCode
    resources.dynamicCode resources.totalQueries resources.structuralCode resources.instructionCode
    resources.handlerCode resources.solverPortCode

end PolynomialResources

/-- Transport derived pointwise certificates into the single fixed family
backend. This is an assembly lemma; public security proofs supply certificates
of the actual constructed reductions and derive their polynomial runtime. -/
theorem solver_nonuniform
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (solver : ∀ n, AlgebraicGroupModel.DLog11Adversary (F n) (G₁ n) (G₂ n))
    (time : Nat → Nat) (hTime : PolynomiallyBounded time)
    (certificates : ∀ n, dlogWithin (parameters n).rep (parameters n).backend
      (parameters n).descriptionSizes (parameters n).factor (parameters n).description
      (parameters n).generator (parameters n).keyGenerator (parameters n).inputWidth
      (parameters n).solverCode (time n) (solver n)) :
    dlogNonuniformWithin config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).keyGenerator)
      (fun n => (parameters n).inputWidth) solver := by
  have hFactor : PolynomiallyBounded (fun n => (parameters n).factor) :=
    (PolynomiallyBounded.const config.factor).of_le (fun n =>
      le_of_eq (congrArg Configuration.factor (fixed n)))
  refine ⟨fun n => (certificates n).1, ?_⟩
  apply config.nonuniformWithin_of_pointwise _ _ _
    (fun n => (parameters n).solverCode) time _ resources.inputWidth
    (resources.solverCode hFactor) hTime
  intro n
  have h := (certificates n).2
  change ((parameters n).configuration).within _ _ _ _ _ _ at h
  rw [fixed n] at h
  exact h

/-- Both actual list-cache reductions belong to the same fixed polynomial
code/time class. The pointwise implementation certificates supply all execution
and challenge-size obligations. The attacker can use general backend code. -/
theorem reductions_nonuniform
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n)) :
    dlogNonuniformWithin config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).keyGenerator)
      (fun n => (parameters n).inputWidth)
      (fun n => Model.LazyAGM.WeightedReduction.goodReductionList ((index n).sourceTerms (parameters n).cost) (adversary n).source) ∧
    dlogNonuniformWithin config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).keyGenerator)
      (fun n => (parameters n).inputWidth)
      (fun n => Model.LazyAGM.WeightedReduction.badReductionList ((index n).sourceTerms (parameters n).cost) (adversary n).source) := by
  have certificates := fun n => reductions_within (parameters n) (adversary n)
  exact ⟨solver_nonuniform parameters config fixed resources _ _ resources.goodTime
    (fun n => (certificates n).1),
    solver_nonuniform parameters config fixed resources _ _ resources.badTime
    (fun n => (certificates n).2)⟩

end Family

end Signatures.Runtime.WeightedAGM.General
