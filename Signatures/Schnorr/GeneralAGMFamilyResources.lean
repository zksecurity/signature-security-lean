import Signatures.Schnorr.Proofs.GeneralAGM
import Signatures.Runtime.BackendSchnorrAGMPolynomial
import Signatures.Runtime.BackendSchnorrAGMDLogFamily

/-! Polynomial resources for general Schnorr AGM attackers in one fixed
backend. The complete solver's time and stored-code bounds are derived from
the actual native program and component allowances, including every challenge. -/

open OracleComp OracleSpec PFunctor
open Signatures.Runtime Signatures.Runtime.BackendProgram
open Signatures.Runtime.SchnorrAGM.Native
open Signatures.Runtime.SchnorrAGM.Native.Solver.Family

namespace Schnorr.GeneralAGM

universe v w x

variable {C : StepClass.{0, v}} [C.HasProd] [C.HasSum] [C.HasOption]
  {Q : QuantitativeStepClass.{0, v, w} C}
  [Q.HasCategory] [Q.HasProd] [Q.HasSum] [Q.HasOption] [Q.IsDistributive] [OptionCode (Q := Q)]

/-- The execution/description convention fixed before quantifying over solvers.
Constancy across parameters rules out changing the backend or cost convention
to suit an individual member of the family. -/
def Parameters.configuration {F G M : Type} [Field F] [SampleableType F]
    [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [DecidableEq M]
    (P : Parameters (Q := Q) (F := F) (G := G) (M := M)) : Configuration.{v, w, x} Q unifSpec :=
  ⟨P.iface, P.control, P.queryCost, P.backend, P.descriptionSizes, P.factor, P.description⟩

namespace Family

variable {F G M : Nat → Type}
  [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
  [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
  [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]
  (parameters : ∀ n, Parameters (Q := Q) (F := F n) (G := G n) (M := M n))

/-- Fixed polynomials for caller resources, encoded widths and local operation
prices. Solver time/code are conclusions, never fields. Neither numerical field
size, random arity nor message-domain cardinality is required to be polynomial. -/
structure PolynomialResources : Prop where
  overhead : PolynomialOverhead (fun n => (parameters n).overhead)
  work : PolynomiallyBounded (fun n => (parameters n).execution.work)
  randomQueries : PolynomiallyBounded (fun n => (parameters n).queries.random)
  hashQueries : PolynomiallyBounded (fun n => (parameters n).queries.hash)
  signingQueries : PolynomiallyBounded (fun n => (parameters n).queries.sign)
  inputWidth : PolynomiallyBounded (fun n => (parameters n).inputWidth)
  width : PolynomiallyBounded (fun n => (parameters n).width)
  outputWidth : PolynomiallyBounded (fun n => (parameters n).outputWidth)
  routeWidth : PolynomiallyBounded (fun n => (parameters n).routeWidth)
  portWidth : PolynomiallyBounded (fun n => (parameters n).portWidth)
  tickTime : PolynomiallyBounded (fun n => (parameters n).tickTime)
  adapterTime : PolynomiallyBounded (fun n => (parameters n).adapterTime)
  divisionTime : PolynomiallyBounded (fun n => (parameters n).divisionTime)
  times : Handler.PolynomialTimes (fun n => (parameters n).times)
  callerCode : PolynomiallyBounded (fun n => (parameters n).callerCodeLimit)
  samplerCode : PolynomiallyBounded (fun n => (parameters n).sampler.descriptionSize (parameters n).descriptionSizes)
  structuralCode : PolynomiallyBounded (fun n => (parameters n).allowance)
  instructionCode : PolynomiallyBounded (fun n => (parameters n).instructionSize)
  randomPortCode : PolynomiallyBounded (fun n => (parameters n).randomPortSize)
  handlerPortCode : PolynomiallyBounded (fun n => (parameters n).handlerPortSize)
  solverPortCode : PolynomiallyBounded (fun n => (parameters n).solverPortSize)

namespace PolynomialResources

variable {parameters} (resources : PolynomialResources parameters)

include resources

theorem totalQueries : PolynomiallyBounded (fun n => (parameters n).queries.total) :=
  (resources.randomQueries.add resources.hashQueries).add resources.signingQueries

theorem executionQueries : PolynomiallyBounded (fun n => (parameters n).execution.queries) :=
  resources.totalQueries.of_le (fun n => (parameters n).queryCapacity)

theorem solverTime : PolynomiallyBounded (fun n => (parameters n).solverTime) := by
  exact Solver.programTime_polynomial (fun n => (parameters n).overhead) (fun n => (parameters n).execution)
    (fun n => (parameters n).inputWidth) (fun n => (parameters n).width)
    (fun n => (parameters n).outputWidth) (fun n => (parameters n).routeWidth)
    (fun n => (parameters n).queries.total) (fun n => (parameters n).queries.total + 2)
    (fun n => (parameters n).queries.total) (fun n => (parameters n).width)
    (fun n => (parameters n).width) (fun n => (parameters n).width) (fun n => (parameters n).portWidth)
    (fun n => (parameters n).queries.total) (fun n => (parameters n).tickTime)
    (fun n => (parameters n).adapterTime) (fun n => (parameters n).divisionTime) (fun n => (parameters n).times)
    resources.overhead resources.work resources.executionQueries resources.inputWidth resources.width
    resources.outputWidth resources.routeWidth resources.totalQueries
    (resources.totalQueries.add (PolynomiallyBounded.const 2)) resources.totalQueries
    resources.width resources.width resources.width resources.portWidth resources.totalQueries
    resources.tickTime resources.adapterTime resources.divisionTime resources.times

theorem solverCode (hFactor : PolynomiallyBounded (fun n => (parameters n).factor)) :
    PolynomiallyBounded (fun n => (parameters n).solverCode) := by
  exact Solver.programDescription_polynomial (fun n => (parameters n).factor)
    (fun n => (parameters n).callerCodeLimit)
    (fun n => (parameters n).sampler.descriptionSize (parameters n).descriptionSizes)
    (fun n => (parameters n).randomPortSize) (fun n => (parameters n).handlerPortSize)
    (fun n => (parameters n).solverPortSize) (fun n => (parameters n).queries.total)
    (fun n => (parameters n).allowance) (fun n => (parameters n).instructionSize)
    hFactor resources.callerCode resources.samplerCode resources.randomPortCode resources.handlerPortCode
    resources.solverPortCode resources.totalQueries resources.structuralCode resources.instructionCode

end PolynomialResources

variable [∀ n, DecidableEq (Interface.SourceRequest (F n) (G n) (M n))]

/-- The actual DLog reduction belongs to the fixed polynomial-time/code class.
Its resource witness follows from the pointwise native implementation proof. -/
theorem reduction_nonuniform
    (config : Configuration.{v, w, x} Q unifSpec)
    (fixed : ∀ n, (parameters n).configuration = config)
    (resources : PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n)) :
    dlogNonuniformWithin config (fun n => (parameters n).rep)
      (fun n => (parameters n).generator) (fun n => (parameters n).inputWidth)
      (fun n => SchnorrAGM.dlogReduction (adversary n).source) := by
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

end Schnorr.GeneralAGM
