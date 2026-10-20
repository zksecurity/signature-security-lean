import Signatures.Runtime.Caliper.WeightedSecurity
import Signatures.Runtime.Caliper.DLogFamily
import Signatures.Runtime.Caliper.PolynomialBounds

/-! Polynomial resources for both complete weighted Caliper reductions. Only
local routine costs, caller allowances, encoding widths and capacities are
premises. Complete solver code, time and total memory are derived. No finite
index/message domain or polynomial numerical sampling range is required. -/
namespace Signatures.Runtime.WeightedCaliper.Family
open Caliper CaliperBackend
variable {F G PK J M : Nat → Type} [∀ n, Field (F n)] [∀ n, SampleableType (F n)] [∀ n, DecidableEq (J n)]
    [∀ n, AddCommGroup (G n)] [∀ n, Module (F n) (G n)]
    [∀ n, AddCommGroup (PK n)] [∀ n, Module (F n) (PK n)]
    {queries : Nat → QueryAllowance} {terms : ∀ n, M n → List (J n × F n)}
    {generator : ∀ n, G n} {keyGenerator : ∀ n, PK n}
    (parameters : ∀ n, Parameters (F n) (G n) (PK n) (J n) (M n) (queries n) (terms n) (generator n) (keyGenerator n))

structure PolynomialResources : Prop where
  queries : PolynomiallyBounded (fun n => (queries n).total)
  wordBits : PolynomiallyBounded (fun n => (parameters n).wordBits)
  indexWidth : PolynomiallyBounded (fun n => (parameters n).layout.scheme.rows.accumulation.cache.key.representation.encoding.words)
  messageWidth : PolynomiallyBounded (fun n => (parameters n).layout.scheme.rows.message.representation.encoding.words)
  scalarWidth : PolynomiallyBounded (fun n => (parameters n).scalar.representation.encoding.words)
  pointWidth : PolynomiallyBounded (fun n => (parameters n).layout.scheme.rows.point.representation.encoding.words)
  keyWidth : PolynomiallyBounded (fun n => (parameters n).layout.key.representation.encoding.words)
  stateWidth : PolynomiallyBounded (fun n => (parameters n).layout.state.encoding.words)
  cacheCapacity : PolynomiallyBounded (fun n => (parameters n).layout.scheme.rows.accumulation.cache.capacityPred)
  hashCapacity : PolynomiallyBounded (fun n => (parameters n).layout.scheme.hashes)
  signCapacity : PolynomiallyBounded (fun n => (parameters n).layout.scheme.signs)
  gammaCapacity : PolynomiallyBounded (fun n => (parameters n).layout.scheme.gamma)
  xiCapacity : PolynomiallyBounded (fun n => (parameters n).layout.scheme.xi)
  weightedTerms : PolynomiallyBounded (fun n => (parameters n).layout.scheme.terms)
  goodNames : PolynomiallyBounded (fun n => (parameters n).good.slots)
  badNames : PolynomiallyBounded (fun n => (parameters n).bad.slots)
  keyNames : PolynomiallyBounded (fun n => (parameters n).keySlots)
  samplerNames : PolynomiallyBounded (fun n => (parameters n).samplerSlots)
  callerNames : PolynomiallyBounded (fun n => (parameters n).callerLimits.slots)
  keyTime : PolynomiallyBounded (fun n => (parameters n).keyBudget.time)
  keyWords : PolynomiallyBounded (fun n => (parameters n).keyBudget.words)
  samplerTime : PolynomiallyBounded (fun n => (parameters n).samplerBudget.time)
  samplerWords : PolynomiallyBounded (fun n => (parameters n).samplerBudget.words)
  localTime : PolynomiallyBounded (fun n => (parameters n).callerLimits.step.time)
  localWords : PolynomiallyBounded (fun n => (parameters n).callerLimits.step.words)
  initialTime : PolynomiallyBounded (fun n => (parameters n).callerLimits.initial.time)
  initialWords : PolynomiallyBounded (fun n => (parameters n).callerLimits.initial.words)
  goodGeneratorTime : PolynomiallyBounded (fun n => ((parameters n).goodBounds.generator).time)
  goodGeneratorWords : PolynomiallyBounded (fun n => ((parameters n).goodBounds.generator).words)
  goodUpdateTime : PolynomiallyBounded (fun n => ((parameters n).goodBounds.update).time)
  goodUpdateWords : PolynomiallyBounded (fun n => ((parameters n).goodBounds.update).words)
  goodHashTime : PolynomiallyBounded (fun n => ((parameters n).goodBounds.response false).time)
  goodHashWords : PolynomiallyBounded (fun n => ((parameters n).goodBounds.response false).words)
  goodSignTime : PolynomiallyBounded (fun n => ((parameters n).goodBounds.response true).time)
  goodSignWords : PolynomiallyBounded (fun n => ((parameters n).goodBounds.response true).words)
  goodExtractTime : PolynomiallyBounded (fun n => ((parameters n).goodBounds.extract).time)
  goodExtractWords : PolynomiallyBounded (fun n => ((parameters n).goodBounds.extract).words)
  goodSumTime : PolynomiallyBounded (fun n => ((parameters n).goodBounds.sum).time)
  goodSumWords : PolynomiallyBounded (fun n => ((parameters n).goodBounds.sum).words)
  badGeneratorTime : PolynomiallyBounded (fun n => ((parameters n).badBounds.generator).time)
  badGeneratorWords : PolynomiallyBounded (fun n => ((parameters n).badBounds.generator).words)
  badUpdateTime : PolynomiallyBounded (fun n => ((parameters n).badBounds.update).time)
  badUpdateWords : PolynomiallyBounded (fun n => ((parameters n).badBounds.update).words)
  badHashTime : PolynomiallyBounded (fun n => ((parameters n).badBounds.response false).time)
  badHashWords : PolynomiallyBounded (fun n => ((parameters n).badBounds.response false).words)
  badSignTime : PolynomiallyBounded (fun n => ((parameters n).badBounds.response true).time)
  badSignWords : PolynomiallyBounded (fun n => ((parameters n).badBounds.response true).words)
  badExtractTime : PolynomiallyBounded (fun n => ((parameters n).badBounds.extract).time)
  badExtractWords : PolynomiallyBounded (fun n => ((parameters n).badBounds.extract).words)
  badSumTime : PolynomiallyBounded (fun n => ((parameters n).badBounds.sum).time)
  badSumWords : PolynomiallyBounded (fun n => ((parameters n).badBounds.sum).words)

namespace PolynomialResources
variable {parameters} (resources : PolynomialResources parameters)
include resources

theorem goodSetupWidth : PolynomiallyBounded (fun n => (parameters n).layout.goodSetup.width) := by
  cases resources
  caliper_polynomial

theorem badSetupWidth : PolynomiallyBounded (fun n => (parameters n).layout.badSetup.width) := by
  cases resources
  caliper_polynomial

theorem challengeWidth : PolynomiallyBounded (fun n => (parameters n).layout.goodSetup.challenge.representation.encoding.words) := by
  cases resources
  caliper_polynomial

theorem goodNameBudget : PolynomiallyBounded (fun n => (parameters n).goodNames) := by
  cases resources
  caliper_polynomial

theorem badNameBudget : PolynomiallyBounded (fun n => (parameters n).badNames) := by
  cases resources
  caliper_polynomial

theorem goodExtractionTime : PolynomiallyBounded (fun n =>
    WeightedExtractor.timeBudget (base := base (F n) (J n)) (key := indexTy) (val := scalarTy)
      (parameters n).layout.good.extraction (parameters n).goodBounds.generator.time (parameters n).samplerBudget.time
      (parameters n).goodBounds.update.time (parameters n).goodBounds.extract.time (parameters n).goodBounds.sum.time) := by
  cases resources
  caliper_polynomial

theorem goodTime : PolynomiallyBounded (fun n => (parameters n).goodTime) := by
  have setup := resources.goodSetupWidth
  have extraction := resources.goodExtractionTime
  cases resources
  caliper_polynomial

theorem goodExtractionWords : PolynomiallyBounded (fun n =>
    WeightedExtractor.codeBudget (base := base (F n) (J n)) (key := indexTy) (val := scalarTy)
      (parameters n).layout.good.extraction (parameters n).goodBounds.generator.words (parameters n).samplerBudget.words
      (parameters n).goodBounds.update.words (parameters n).goodBounds.extract.words (parameters n).goodBounds.sum.words) := by
  cases resources
  caliper_polynomial

theorem goodWords : PolynomiallyBounded (fun n => (parameters n).goodWords) := by
  have setup := resources.goodSetupWidth
  have extraction := resources.goodExtractionWords
  cases resources
  caliper_polynomial

theorem badCallerWidth : PolynomiallyBounded (fun n => CallerStep.width (parameters n).layout.bad.control) := by
  cases resources
  caliper_polynomial

theorem badServiceWidth : PolynomiallyBounded (fun n => WeightedCallerPackets.width (parameters n).layout.bad.service) := by
  cases resources
  caliper_polynomial

theorem badExtractionTime : PolynomiallyBounded (fun n =>
    WeightedExtractor.badTimeBudget (base := base (F n) (J n)) (key := indexTy) (val := pairTy)
      (parameters n).layout.bad.extraction (parameters n).badBounds.generator.time (parameters n).pairTime
      (parameters n).badBounds.update.time (parameters n).badBounds.extract.time) := by
  cases resources
  caliper_polynomial

theorem pairTime : PolynomiallyBounded (fun n => (parameters n).pairTime) := by
  cases resources
  caliper_polynomial

theorem badPreparationTime : PolynomiallyBounded (fun n =>
    WeightedBadSetup.timeBudget (parameters n).layout.preparation
      (parameters n).samplerBudget.time (parameters n).keyBudget.time) := by
  cases resources
  caliper_polynomial

theorem badHandlerTime : PolynomiallyBounded (fun n =>
    WeightedCallerHandler.timeBudget (base := base (F n) (J n)) (key := indexTy) (val := pairTy)
      (parameters n).layout.bad.service (parameters n).layout.bad.terms
      (parameters n).layout.bad.termCountFits (parameters n).layout.bad.termStorageFits
      (parameters n).layout.randomBound (parameters n).layout.randomFits
      (parameters n).badBounds.generator.time (parameters n).pairTime (parameters n).badBounds.update.time
      (fun signing => ((parameters n).badBounds.response signing).time)) := by
  have paired := resources.pairTime
  have width := resources.badServiceWidth
  cases resources
  caliper_polynomial

theorem badTailTime : PolynomiallyBounded (fun n =>
    WeightedCallerProgram.timeBudget (base := base (F n) (J n)) (key := indexTy) (val := pairTy)
      (parameters n).layout.bad false (parameters n).layout.key.representation.encoding.words
      (parameters n).badBounds.generator.time (parameters n).pairTime (parameters n).badBounds.update.time
      (fun signing => ((parameters n).badBounds.response signing).time)
      (parameters n).callerLimits.step.time (parameters n).callerLimits.initial.time (queries n).total
      (parameters n).badBounds.extract.time (parameters n).badBounds.sum.time) := by
  have extraction := resources.badExtractionTime
  have handler := resources.badHandlerTime
  have width := resources.badCallerWidth
  simp only [WeightedCallerProgram.timeBudget, WeightedCallerProgram.extractionTime,
    Bool.false_eq_true, ite_false]
  cases resources
  caliper_polynomial

theorem badTime : PolynomiallyBounded (fun n => (parameters n).badTime) :=
  resources.badPreparationTime.add (((PolynomiallyBounded.const 200).mul resources.badSetupWidth).add resources.badTailTime)

theorem badExtractionWords : PolynomiallyBounded (fun n =>
    WeightedExtractor.badCodeBudget (base := base (F n) (J n)) (key := indexTy) (val := pairTy)
      (parameters n).layout.bad.extraction (parameters n).badBounds.generator.words (parameters n).pairWords
      (parameters n).badBounds.update.words (parameters n).badBounds.extract.words) := by
  cases resources
  caliper_polynomial

theorem pairWords : PolynomiallyBounded (fun n => (parameters n).pairWords) := by
  cases resources
  caliper_polynomial

theorem badPreparationWords : PolynomiallyBounded (fun n =>
    WeightedBadSetup.codeBudget (parameters n).layout.preparation
      (parameters n).samplerBudget.words (parameters n).keyBudget.words) := by
  cases resources
  caliper_polynomial

theorem badHandlerWords : PolynomiallyBounded (fun n =>
    WeightedCallerHandler.codeBudget (base := base (F n) (J n)) (key := indexTy) (val := pairTy)
      (parameters n).layout.bad.service (parameters n).layout.bad.terms
      (parameters n).layout.bad.termCountFits (parameters n).layout.bad.termStorageFits
      (parameters n).layout.randomBound (parameters n).layout.randomFits
      (parameters n).badBounds.generator.words (parameters n).pairWords (parameters n).badBounds.update.words
      (fun signing => ((parameters n).badBounds.response signing).words)) := by
  have paired := resources.pairWords
  have width := resources.badServiceWidth
  cases resources
  caliper_polynomial

theorem badTailWords : PolynomiallyBounded (fun n =>
    WeightedCallerProgram.codeBudget (base := base (F n) (J n)) (key := indexTy) (val := pairTy)
      (parameters n).layout.bad false (parameters n).layout.key.representation.encoding.words
      (parameters n).badBounds.generator.words (parameters n).pairWords (parameters n).badBounds.update.words
      (fun signing => ((parameters n).badBounds.response signing).words)
      (parameters n).callerLimits.step.words (parameters n).callerLimits.initial.words (queries n).total
      (parameters n).badBounds.extract.words (parameters n).badBounds.sum.words) := by
  have extraction := resources.badExtractionWords
  have handler := resources.badHandlerWords
  have width := resources.badCallerWidth
  simp only [WeightedCallerProgram.codeBudget, WeightedCallerProgram.extractionWords,
    Bool.false_eq_true, ite_false]
  cases resources
  caliper_polynomial

theorem badWords : PolynomiallyBounded (fun n => (parameters n).badWords) :=
  (resources.badPreparationWords.add ((((PolynomiallyBounded.const 700).mul resources.badSetupWidth).add
    (PolynomiallyBounded.const 252)).add resources.badTailWords)).add (PolynomiallyBounded.const 1)

theorem goodMemory : PolynomiallyBounded (fun n => (parameters n).goodMemory) :=
  (((((PolynomiallyBounded.const 5).mul resources.goodWords).add
    ((PolynomiallyBounded.const 4).mul resources.goodNameBudget)).add (PolynomiallyBounded.const 3)).add
      resources.challengeWidth).add resources.goodTime

theorem badMemory : PolynomiallyBounded (fun n => (parameters n).badMemory) :=
  (((((PolynomiallyBounded.const 5).mul resources.badWords).add
    ((PolynomiallyBounded.const 4).mul resources.badNameBudget)).add (PolynomiallyBounded.const 3)).add
      resources.challengeWidth).add resources.badTime

theorem solverCode : PolynomiallyBounded (fun n => (parameters n).solverCode) :=
  resources.goodWords.max resources.badWords
theorem solverMemory : PolynomiallyBounded (fun n => (parameters n).solverMemory) :=
  resources.goodMemory.max resources.badMemory
end PolynomialResources

/-- Hardness against every polynomial-resource solver in the fixed Caliper family. -/
def dlogHardness : Prop := dlogNonuniformHardness (fun n => (parameters n).layout.port)
  (fun n => (parameters n).layout.goodSetup.challenge) (fun n => (parameters n).scalar) generator keyGenerator

theorem reductions_nonuniform (resources : PolynomialResources parameters)
    (adversary : ∀ n, AlgebraicAdversary (parameters n)) :
    dlogNonuniformWithin (fun n => (parameters n).layout.port)
      (fun n => (parameters n).layout.goodSetup.challenge) (fun n => (parameters n).scalar)
      generator keyGenerator (fun n => Model.LazyAGM.WeightedReduction.goodReductionList (terms n) (adversary n).proofView) ∧
    dlogNonuniformWithin (fun n => (parameters n).layout.port)
      (fun n => (parameters n).layout.goodSetup.challenge) (fun n => (parameters n).scalar)
      generator keyGenerator (fun n => Model.LazyAGM.WeightedReduction.badReductionList (terms n) (adversary n).proofView) := by
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
end Signatures.Runtime.WeightedCaliper.Family
