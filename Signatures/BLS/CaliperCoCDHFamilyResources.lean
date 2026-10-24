import Proofs.BLS.CaliperCoCDH
import Proofs.Runtime.Caliper.CoCDHFamily
import Proofs.Runtime.Caliper.PolynomialBounds

/-! Polynomial complete Coron resources follow from polynomial component
costs, encoding widths, capacities and caller allowances. No bound on the
cardinality of the message space, scalar field or sampling range is required. -/
namespace BLS.CaliperCoCDH.Family
open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend
variable {F G K M : Nat → Type} [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
    [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
    [∀ n, AddCommGroup (K n)] [∀ n, Module (F n) (K n)] [∀ n, DecidableEq (M n)]
    {queries : Nat → QueryAllowance} {generator : ∀ n, G n} {keyGenerator : ∀ n, K n}
    (parameters : ∀ n, Parameters (F n) (G n) (K n) (M n) (queries n) (generator n) (keyGenerator n))

structure PolynomialResources : Prop where
  queries : PolynomiallyBounded (fun n => (queries n).total)
  wordBits : PolynomiallyBounded (fun n => (parameters n).wordBits)
  messageWidth : PolynomiallyBounded (fun n => (parameters n).service.cache.key.representation.encoding.words)
  scalarWidth : PolynomiallyBounded (fun n => (parameters n).service.cache.value.representation.encoding.words)
  pointWidth : PolynomiallyBounded (fun n => (parameters n).service.point.representation.encoding.words)
  keyWidth : PolynomiallyBounded (fun n => (parameters n).key.representation.encoding.words)
  stateWidth : PolynomiallyBounded (fun n => (parameters n).layout.state.encoding.words)
  cacheCapacity : PolynomiallyBounded (fun n => (parameters n).service.cache.capacityPred)
  logCapacity : PolynomiallyBounded (fun n => (parameters n).service.capacityPred)
  primitiveNames : PolynomiallyBounded (fun n => (parameters n).routines.slots)
  terminalNames : PolynomiallyBounded (fun n => (parameters n).arithmetic.slots)
  samplerNames : PolynomiallyBounded (fun n => (parameters n).sampler.slots)
  callerNames : PolynomiallyBounded (fun n => (parameters n).callerLimits.slots)
  samplerTime : PolynomiallyBounded (fun n => (parameters n).sampler.time)
  samplerWords : PolynomiallyBounded (fun n => (parameters n).sampler.words)
  localTime : PolynomiallyBounded (fun n => (parameters n).callerLimits.stepTime)
  localWords : PolynomiallyBounded (fun n => (parameters n).callerLimits.stepWords)
  initialTime : PolynomiallyBounded (fun n => (parameters n).callerLimits.initialTime)
  initialWords : PolynomiallyBounded (fun n => (parameters n).callerLimits.initialWords)
  scaleTime : PolynomiallyBounded (fun n => (parameters n).routines.scaleTime)
  scaleWords : PolynomiallyBounded (fun n => (parameters n).routines.scaleWords)
  addTime : PolynomiallyBounded (fun n => (parameters n).routines.addTime)
  addWords : PolynomiallyBounded (fun n => (parameters n).routines.addWords)
  terminalScaleTime : PolynomiallyBounded (fun n => (parameters n).arithmetic.scaleTime)
  terminalScaleWords : PolynomiallyBounded (fun n => (parameters n).arithmetic.scaleWords)
  subTime : PolynomiallyBounded (fun n => (parameters n).arithmetic.subTime)
  subWords : PolynomiallyBounded (fun n => (parameters n).arithmetic.subWords)

namespace PolynomialResources
variable {parameters} (resources : PolynomialResources parameters)
include resources

omit [∀ n, DecidableEq (M n)] in
theorem signingQueries : PolynomiallyBounded (fun n => (queries n).sign) :=
  resources.queries.of_le (fun n => by unfold QueryAllowance.total; omega)

omit [∀ n, DecidableEq (M n)] in
theorem inputWidth : PolynomiallyBounded (fun n => (parameters n).layout.input.encoding.words) := by
  have equal : (fun n => (parameters n).layout.input.encoding.words) =
      (fun n => (parameters n).key.representation.encoding.words) := by
    funext n
    rw [(parameters n).input_eq]
  rw [equal]
  exact resources.keyWidth

omit [∀ n, DecidableEq (M n)] in
theorem challengeWidth : PolynomiallyBounded (fun n => (parameters n).challenge.representation.encoding.words) := by
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem names : PolynomiallyBounded (fun n => (parameters n).names) := by
  cases resources
  caliper_polynomial

theorem solverTime : PolynomiallyBounded (fun n => (parameters n).solverTime) := by
  have callerInput : PolynomiallyBounded (fun n => (parameters n).layout.input.encoding.words) := resources.inputWidth
  cases resources
  caliper_polynomial

theorem solverCode : PolynomiallyBounded (fun n => (parameters n).solverCode) := by
  have callerInput : PolynomiallyBounded (fun n => (parameters n).layout.input.encoding.words) := resources.inputWidth
  cases resources
  caliper_polynomial

theorem solverMemory : PolynomiallyBounded (fun n => (parameters n).solverMemory) := by
  have callerInput : PolynomiallyBounded (fun n => (parameters n).layout.input.encoding.words) := resources.inputWidth
  have code : PolynomiallyBounded (fun n => (parameters n).solverCode) := resources.solverCode
  have time : PolynomiallyBounded (fun n => (parameters n).solverTime) := resources.solverTime
  have names : PolynomiallyBounded (fun n => (parameters n).names) := resources.names
  cases resources
  caliper_polynomial

end PolynomialResources

def coCDHHardness [∀ n, SampleableType (G n)] : Prop :=
  coCDHNonuniformHardness (F := F) (fun n => (parameters n).service.port)
    (fun n => (parameters n).challenge) (fun n => (parameters n).service.point) generator keyGenerator

theorem reduction_nonuniform (resources : PolynomialResources parameters)
    (adversary : ∀ n, Adversary (parameters n))
    (generates : ∀ n, Function.Surjective (fun scalar : F n => scalar • generator n)) :
    coCDHNonuniformWithin (F := F) (fun n => (parameters n).service.port)
      (fun n => (parameters n).challenge) (fun n => (parameters n).service.point) generator keyGenerator
      (fun n => CoCDH.coronReductionLazyPK (F := F n) (queries n).sign (ROM.cacheForgeryPK (adversary n).source)) :=
  coCDHNonuniformWithin.of_pointwise (F := F) _ _ _ _ _ _
    (fun n => (parameters n).solverCode) (fun n => (parameters n).solverMemory) (fun n => (parameters n).solverTime)
    resources.wordBits resources.solverCode resources.solverMemory resources.solverTime
    (fun n => reduction_within (parameters n) (adversary n) (generates n))

end BLS.CaliperCoCDH.Family
