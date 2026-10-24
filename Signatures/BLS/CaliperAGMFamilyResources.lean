import Proofs.BLS.CaliperAGM
import Proofs.Runtime.Caliper.DLogFamily
import Proofs.Runtime.Caliper.PolynomialBounds

/-! Polynomial resources for the concrete Caliper BLS AGM implementation.
Only primitive costs, caller limits, base encoding widths and capacities are
premises. Complete reduction time, code and total memory are derived below.
The word width is polynomial too; no field/message cardinality or numerical
uniform-query range is required to be polynomial. Sampling still uses the explicitly fixed ideal uniform port. -/
namespace BLS.CaliperAGM.Family
open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend
variable {F G K M : Nat → Type} [∀ n, Field (F n)] [∀ n, SampleableType (F n)]
    [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
    [∀ n, AddCommGroup (K n)] [∀ n, Module (F n) (K n)] [∀ n, DecidableEq (M n)]
    {queries : Nat → QueryAllowance} {generator : ∀ n, G n} {keyGenerator : ∀ n, K n}
    (parameters : ∀ n, Parameters (F n) (G n) (K n) (M n) (queries n) (generator n) (keyGenerator n))

/-- One polynomial per component across the whole parameter family. These
are bounds on the inputs to the reduction's resource calculation. -/
structure PolynomialResources : Prop where
  queries : PolynomiallyBounded (fun n => (queries n).total)
  wordBits : PolynomiallyBounded (fun n => (parameters n).wordBits)
  messageWidth : PolynomiallyBounded (fun n => (parameters n).layout.scheme.cache.key.representation.encoding.words)
  scalarWidth : PolynomiallyBounded (fun n => (parameters n).layout.scheme.cache.value.representation.encoding.words)
  pointWidth : PolynomiallyBounded (fun n => (parameters n).layout.scheme.point.representation.encoding.words)
  keyWidth : PolynomiallyBounded (fun n => (parameters n).layout.key.representation.encoding.words)
  stateWidth : PolynomiallyBounded (fun n => (parameters n).layout.state.encoding.words)
  cacheCapacity : PolynomiallyBounded (fun n => (parameters n).layout.scheme.cache.capacityPred)
  transcriptCapacity : PolynomiallyBounded (fun n => (parameters n).layout.tokens.capacity)
  coefficientCapacity : PolynomiallyBounded (fun n => (parameters n).layout.tokens.coefficients)
  primitiveNames : PolynomiallyBounded (fun n => (parameters n).routines.slots)
  samplerNames : PolynomiallyBounded (fun n => (parameters n).samplerSlots)
  callerNames : PolynomiallyBounded (fun n => (parameters n).callerLimits.names)
  samplerTime : PolynomiallyBounded (fun n => (parameters n).samplerBudget.time)
  samplerWords : PolynomiallyBounded (fun n => (parameters n).samplerBudget.words)
  localTime : PolynomiallyBounded (fun n => (parameters n).callerLimits.step.time)
  localWords : PolynomiallyBounded (fun n => (parameters n).callerLimits.step.words)
  initialTime : PolynomiallyBounded (fun n => (parameters n).callerLimits.initial.time)
  initialWords : PolynomiallyBounded (fun n => (parameters n).callerLimits.initial.words)
  mulTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.mul.time)
  mulWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.mul.words)
  addTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.add.time)
  addWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.add.words)
  subTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.sub.time)
  subWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.sub.words)
  negTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.neg.time)
  negWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.neg.words)
  divideTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.divide.time)
  divideWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.divide.words)
  scaleTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.scale.time)
  scaleWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.scale.words)
  groupAddTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.groupAdd.time)
  groupAddWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.groupAdd.words)
  keyTime : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.key.time)
  keyWords : PolynomiallyBounded (fun n => (parameters n).primitiveBounds.key.words)

namespace PolynomialResources
variable {parameters} (resources : PolynomialResources parameters)
include resources

omit [∀ n, DecidableEq (M n)] in
theorem randomQueries : PolynomiallyBounded (fun n => (queries n).random) :=
  resources.queries.of_le (fun n => by unfold QueryAllowance.total; omega)

omit [∀ n, DecidableEq (M n)] in
theorem hashQueries : PolynomiallyBounded (fun n => (queries n).hash) :=
  resources.queries.of_le (fun n => by unfold QueryAllowance.total; omega)

omit [∀ n, DecidableEq (M n)] in
theorem signingQueries : PolynomiallyBounded (fun n => (queries n).sign) :=
  resources.queries.of_le (fun n => by unfold QueryAllowance.total; omega)

omit [∀ n, DecidableEq (M n)] in
theorem setupWidth : PolynomiallyBounded (fun n => (parameters n).layout.setup.width) := by
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem challengeWidth : PolynomiallyBounded (fun n => (parameters n).layout.setup.challenge.representation.encoding.words) := by
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem names : PolynomiallyBounded (fun n => (parameters n).names) := by
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem goodExtractionTime : PolynomiallyBounded (fun n =>
    BLSFull.goodExtractionTime (base := base (F n) (M n)) (key := messageTy) (val := scalarTy)
      (parameters n).layout (parameters n).routines (parameters n).primitiveBounds (parameters n).samplerBudget.time) := by
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem badExtractionTime : PolynomiallyBounded (fun n =>
    BLSFull.badExtractionTime (base := base (F n) (M n)) (key := messageTy) (val := scalarTy)
      (parameters n).layout (parameters n).routines (parameters n).primitiveBounds (parameters n).samplerBudget.time) := by
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem goodExtractionWords : PolynomiallyBounded (fun n =>
    BLSFull.goodExtractionWords (base := base (F n) (M n)) (key := messageTy) (val := scalarTy)
      (parameters n).layout (parameters n).routines (parameters n).primitiveBounds (parameters n).samplerBudget.words) := by
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem badExtractionWords : PolynomiallyBounded (fun n =>
    BLSFull.badExtractionWords (base := base (F n) (M n)) (key := messageTy) (val := scalarTy)
      (parameters n).layout (parameters n).routines (parameters n).primitiveBounds (parameters n).samplerBudget.words) := by
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem goodTime : PolynomiallyBounded (fun n => (parameters n).goodTime) := by
  have hRandom := resources.randomQueries
  have hHash := resources.hashQueries
  have hSign := resources.signingQueries
  have hSetup := resources.setupWidth
  have hExtract := resources.goodExtractionTime
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem badTime : PolynomiallyBounded (fun n => (parameters n).badTime) := by
  have hRandom := resources.randomQueries
  have hHash := resources.hashQueries
  have hSign := resources.signingQueries
  have hSetup := resources.setupWidth
  have hExtract := resources.badExtractionTime
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem goodWords : PolynomiallyBounded (fun n => (parameters n).goodWords) := by
  have hRandom := resources.randomQueries
  have hHash := resources.hashQueries
  have hSign := resources.signingQueries
  have hSetup := resources.setupWidth
  have hExtract := resources.goodExtractionWords
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem badWords : PolynomiallyBounded (fun n => (parameters n).badWords) := by
  have hRandom := resources.randomQueries
  have hHash := resources.hashQueries
  have hSign := resources.signingQueries
  have hSetup := resources.setupWidth
  have hExtract := resources.badExtractionWords
  cases resources
  caliper_polynomial

omit [∀ n, DecidableEq (M n)] in
theorem goodMemory : PolynomiallyBounded (fun n => (parameters n).goodMemory) :=
  (((((PolynomiallyBounded.const 5).mul resources.goodWords).add
    ((PolynomiallyBounded.const 4).mul resources.names)).add (PolynomiallyBounded.const 3)).add
      resources.challengeWidth).add resources.goodTime

omit [∀ n, DecidableEq (M n)] in
theorem badMemory : PolynomiallyBounded (fun n => (parameters n).badMemory) :=
  (((((PolynomiallyBounded.const 5).mul resources.badWords).add
    ((PolynomiallyBounded.const 4).mul resources.names)).add (PolynomiallyBounded.const 3)).add
      resources.challengeWidth).add resources.badTime

omit [∀ n, DecidableEq (M n)] in
theorem solverCode : PolynomiallyBounded (fun n => (parameters n).solverCode) :=
  resources.goodWords.max resources.badWords

omit [∀ n, DecidableEq (M n)] in
theorem solverMemory : PolynomiallyBounded (fun n => (parameters n).solverMemory) :=
  resources.goodMemory.max resources.badMemory

end PolynomialResources
/-- The fixed Caliper family used by the concrete parameters, quantified over
all polynomial-resource solvers rather than only the two BLS reductions. -/
def dlogHardness : Prop :=
  dlogNonuniformHardness (fun n => (parameters n).layout.port)
    (fun n => (parameters n).layout.setup.challenge) (fun n => (parameters n).layout.scheme.cache.value)
    generator keyGenerator

/-- Both original reductions are polynomial-resource Caliper families, derived
from component bounds and the attacker's local implementation certificates. -/
theorem reductions_nonuniform (resources : PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n)) :
    dlogNonuniformWithin (fun n => (parameters n).layout.port)
      (fun n => (parameters n).layout.setup.challenge) (fun n => (parameters n).layout.scheme.cache.value)
      generator keyGenerator (fun n => BLS.LazyAGM.Reduction.goodReductionList (adversary n).proofView) ∧
    dlogNonuniformWithin (fun n => (parameters n).layout.port)
      (fun n => (parameters n).layout.setup.challenge) (fun n => (parameters n).layout.scheme.cache.value)
      generator keyGenerator (fun n => BLS.LazyAGM.Reduction.badReductionList (adversary n).proofView) := by
  have certificates := fun n => reductions_within (parameters n) (adversary n)
  constructor
  · exact dlogNonuniformWithin.of_pointwise _ _ _ _ _ _
      (fun n => (parameters n).solverCode) (fun n => (parameters n).solverMemory)
      (fun n => (parameters n).goodTime) resources.wordBits resources.solverCode
      resources.solverMemory resources.goodTime (fun n => (certificates n).1)
  · exact dlogNonuniformWithin.of_pointwise _ _ _ _ _ _
      (fun n => (parameters n).solverCode) (fun n => (parameters n).solverMemory)
      (fun n => (parameters n).badTime) resources.wordBits resources.solverCode
      resources.solverMemory resources.badTime (fun n => (certificates n).2)

end BLS.CaliperAGM.Family
