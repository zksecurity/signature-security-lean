import Proofs.Schnorr.CaliperAGM
import Proofs.Runtime.Caliper.CyclicDLogFamily
import Proofs.Runtime.Caliper.PolynomialBounds

/-! Polynomial bounds on the original caller, layouts and primitive routines
imply polynomial code, total memory and runtime for the constructed Schnorr
reduction. Numerical scalar-domain size and random-query arity are unrestricted;
encoded widths, capacities and actual sampling costs are accounted for. -/
namespace Schnorr.CaliperAGM.Family
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
variable {F G M : Nat → Type} [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
    [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
    [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)]
    {queries : Nat → QueryAllowance} {generator : ∀ n, G n}
    (parameters : ∀ n, Parameters (F n) (G n) (M n) (queries n) (generator n))

/-- Component assumptions only; complete-solver resources are conclusions. -/
structure PolynomialResources : Prop where
  queries : PolynomiallyBounded (fun n => (queries n).total)
  wordBits : PolynomiallyBounded (fun n => (parameters n).wordBits)
  messageWidth : PolynomiallyBounded (fun n => (parameters n).layout.service.scheme.message.representation.encoding.words)
  scalarWidth : PolynomiallyBounded (fun n => (parameters n).layout.service.scheme.scalar.representation.encoding.words)
  pointWidth : PolynomiallyBounded (fun n => (parameters n).layout.service.scheme.point.representation.encoding.words)
  stateWidth : PolynomiallyBounded (fun n => (parameters n).layout.state.encoding.words)
  groups : PolynomiallyBounded (fun n => (parameters n).layout.service.groups)
  rows : PolynomiallyBounded (fun n => (parameters n).layout.service.rows)
  coefficients : PolynomiallyBounded (fun n => (parameters n).layout.service.coefficients)
  primitiveNames : PolynomiallyBounded (fun n => (parameters n).routines.handler.slots)
  sampleNames : PolynomiallyBounded (fun n => (parameters n).sampleSlots)
  callerNames : PolynomiallyBounded (fun n => (parameters n).callerLimits.names)
  sampleTime : PolynomiallyBounded (fun n => (parameters n).sampleTime)
  sampleWords : PolynomiallyBounded (fun n => (parameters n).sampleWords)
  localTime : PolynomiallyBounded (fun n => (parameters n).callerLimits.localTime)
  localWords : PolynomiallyBounded (fun n => (parameters n).callerLimits.localWords)
  initialTime : PolynomiallyBounded (fun n => (parameters n).callerLimits.initialTime)
  initialWords : PolynomiallyBounded (fun n => (parameters n).callerLimits.initialWords)
  handlerMulTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.mulTime)
  handlerMulWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.mulWords)
  handlerAddTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.addTime)
  handlerAddWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.addWords)
  handlerScaleTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.scaleTime)
  handlerScaleWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.scaleWords)
  handlerSubTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.subTime)
  handlerSubWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.subWords)
  handlerNegateTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.negateTime)
  handlerNegateWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.handler.negateWords)
  scalarSubTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.subTime)
  scalarSubWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.subWords)
  scalarDivTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.divTime)
  scalarDivWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.divWords)

namespace PolynomialResources
variable {parameters} (resources : PolynomialResources parameters)
include resources

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem hashQueries : PolynomiallyBounded (fun n => (queries n).hash) :=
  resources.queries.of_le (fun n => by unfold QueryAllowance.total Model.QueryAllowance.total; omega)
omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem signingQueries : PolynomiallyBounded (fun n => (queries n).sign) :=
  resources.queries.of_le (fun n => by unfold QueryAllowance.total Model.QueryAllowance.total; omega)

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem schemeWidth : PolynomiallyBounded (fun n => (parameters n).layout.service.scheme.width) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem privateStateWidth : PolynomiallyBounded (fun n => (parameters n).layout.service.scheme.state.representation.encoding.words) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem initializedWidth : PolynomiallyBounded (fun n => (parameters n).layout.service.scheme.initialized.representation.encoding.words) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem handlerWidth : PolynomiallyBounded (fun n => (parameters n).layout.service.width) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem callerWidth : PolynomiallyBounded (fun n => CallerStep.width (parameters n).layout.control) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem hashWidth : PolynomiallyBounded (fun n => (parameters n).layout.service.hash.width) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem names : PolynomiallyBounded (fun n => CaliperBackend.SchnorrAGM.Full.nameBudget (parameters n).layout (parameters n).routines (parameters n).callerLimits (parameters n).sampleSlots) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem handlerTime : PolynomiallyBounded (fun n => CaliperBackend.SchnorrAGM.CallerHandler.timeBudget (parameters n).layout.service (parameters n).routines.handler (parameters n).primitiveBounds.handler (parameters n).sampleTime) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  have component0 := resources.schemeWidth
  have component1 := resources.handlerWidth
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem handlerWords : PolynomiallyBounded (fun n => CaliperBackend.SchnorrAGM.CallerHandler.codeBudget (parameters n).layout.service (parameters n).routines.handler (parameters n).primitiveBounds.handler (parameters n).sampleWords) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  have component0 := resources.schemeWidth
  have component1 := resources.handlerWidth
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem extractionTime : PolynomiallyBounded (fun n => CaliperBackend.SchnorrAGM.Extraction.timeBudget (parameters n).layout.service.hash (parameters n).primitiveBounds.handler.mulTime (parameters n).primitiveBounds.handler.addTime (parameters n).primitiveBounds.subTime (parameters n).primitiveBounds.divTime (parameters n).sampleTime) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  have component0 := resources.schemeWidth
  have component1 := resources.hashWidth
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] [∀ n, DecidableEq (G n)] [∀ n, DecidableEq (M n)] in
theorem extractionWords : PolynomiallyBounded (fun n => CaliperBackend.SchnorrAGM.Extraction.codeBudget (parameters n).layout.service.hash (parameters n).primitiveBounds.handler.mulWords (parameters n).primitiveBounds.handler.addWords (parameters n).primitiveBounds.subWords (parameters n).primitiveBounds.divWords (parameters n).sampleWords) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  have component0 := resources.schemeWidth
  have component1 := resources.hashWidth
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] in
theorem solverTime : PolynomiallyBounded (fun n => (parameters n).solverTime) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  have component0 := resources.initializedWidth
  have component1 := resources.callerWidth
  have component2 := resources.handlerTime
  have component3 := resources.extractionTime
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] in
theorem solverCode : PolynomiallyBounded (fun n => (parameters n).solverCode) := by
  have hashBound := resources.hashQueries
  have signBound := resources.signingQueries
  have component0 := resources.initializedWidth
  have component1 := resources.callerWidth
  have component2 := resources.handlerWords
  have component3 := resources.extractionWords
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (F n)] in
theorem solverMemory : PolynomiallyBounded (fun n => (parameters n).solverMemory) := by
  have inputWidth : PolynomiallyBounded (fun n => (parameters n).layout.service.scheme.config.representation.encoding.words) :=
    resources.pointWidth.add resources.pointWidth
  exact (((((PolynomiallyBounded.const 5).mul resources.solverCode).add
    ((PolynomiallyBounded.const 4).mul resources.names)).add (PolynomiallyBounded.const 3)).add inputWidth).add resources.solverTime

end PolynomialResources

/-- Hardness in the fixed Caliper family against every polynomial-resource
solver family, not just the particular Schnorr reduction. -/
def dlogHardness : Prop :=
  cyclicDLogNonuniformHardness (fun n => (parameters n).layout.service.random.port)
    (fun n => (parameters n).layout.service.scheme.config) (fun n => (parameters n).layout.service.scheme.scalar) generator

theorem reduction_nonuniform (resources : PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n)) :
    cyclicDLogNonuniformWithin (fun n => (parameters n).layout.service.random.port)
      (fun n => (parameters n).layout.service.scheme.config) (fun n => (parameters n).layout.service.scheme.scalar)
      generator (fun n => Signatures.Runtime.SchnorrAGM.dlogReduction (adversary n).source) :=
  cyclicDLogNonuniformWithin.of_pointwise _ _ _ _ _
    (fun n => (parameters n).solverCode) (fun n => (parameters n).solverMemory) (fun n => (parameters n).solverTime)
    resources.wordBits resources.solverCode resources.solverMemory resources.solverTime
    (fun n => reduction_within (parameters n) (adversary n))

end Schnorr.CaliperAGM.Family
