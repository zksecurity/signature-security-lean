import Proofs.Runtime.Caliper.WeightedSharedCaller
import Proofs.Runtime.Caliper.PairSamplingMemory
import Proofs.Model.DirectAGM
import Signatures.BLS.QueryAllowance

/-! Fixed Caliper models for weighted AGM signatures. The parameters contain
local routine implementations and costs, one scalar sampler, bounded layouts,
and numeric caller allowances. Both complete solvers and their budgets are
constructed; the attacker supplies just one local caller and source witness. -/
namespace Signatures.Runtime.WeightedCaliper
open Caliper OracleComp OracleSpec CaliperBackend BoundedSource

abbrev scalarTy : Ty Bool := .atom true
abbrev indexTy : Ty Bool := .atom false
abbrev pairTy : Ty Bool := .pair scalarTy scalarTy
abbrev base (F J : Type) : Bool → Type | true => F | false => J
abbrev QueryAllowance := BLS.QueryAllowance
inductive Comparison : Ty Bool → Ty Bool → Type
  | equal : Comparison (.pair indexTy indexTy) .bool
def primitives (F J : Type) [DecidableEq J] : Primitives (base F J) Comparison where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1
def comparison : Expr Comparison [indexTy, indexTy] .bool :=
  .op .equal (.pair (.var .here) (.var (.there .here)))
theorem comparison_correct (F J : Type) [DecidableEq J] (left right : J) :
    comparison.denote (primitives F J) (left, right, ()) = decide (left = right) := rfl

variable (F G PK J M : Type) [Field F] [SampleableType F] [DecidableEq J]
    [AddCommGroup G] [Module F G] [AddCommGroup PK] [Module F PK]
    (queries : QueryAllowance) (terms : M → List (J × F)) (generator : G) (keyGenerator : PK)

structure Parameters where
  wordBits : Nat
  State : Type
  layout : WeightedFull.SharedLayouts wordBits J M G F PK State
  good : WeightedFull.Routines (base := base F J) (key := indexTy) (val := scalarTy) layout.good
  bad : WeightedFull.Routines (base := base F J) (key := indexTy) (val := pairTy) layout.bad
  goodBounds : WeightedFull.Routines.Bounds (base := base F J) (key := indexTy) (val := scalarTy) layout.good good
  badBounds : WeightedFull.Routines.Bounds (base := base F J) (key := indexTy) (val := pairTy) layout.bad bad
  callerLimits : WeightedFull.Caller.Limits
  goodTerms : good.generate = terms
  badTerms : bad.generate = terms
  goodCoefficient : good.coefficientDefault.val = 0
  badCoefficient : bad.coefficientDefault.val = 0
  goodCombine : ∀ value, good.combine value = value.2.2 + value.1 • value.2.1
  badCombine : ∀ value, bad.combine value = value.2.2 + value.1 • value.2.1
  goodResponse : good.respond = fun signing value => value.1 • (if signing then value.2.2 else value.2.1)
  badResponse : bad.respond = fun signing value =>
    if signing then value.2.1 • (value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1)
    else value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1
  goodExtract : good.calculate = fun value => value.1 / (value.2.1 - value.2.2)
  badExtract : bad.calculate = fun value => -(value.2.1.2 - value.2.2.2) / (value.2.1.1 - value.2.2.1)
  goodSum : good.numerator = fun value => value.1 + value.2
  keyScale : Implementation .unit layout.preparation.arguments layout.key (fun value => value.1 • value.2)
  keySlots : Nat
  keyReserve : keySlots + 5 < 2 ^ wordBits
  keyNames : NamesBound keyScale.program.code keySlots
  keyBudget : WeightedFull.Budget
  keyBound : keyScale.BoundedBy keyBudget.time keyBudget.words
  sampler : Interactive.Code wordBits
  scalarSource : ProbComp layout.scheme.rows.accumulation.cache.value.Value
  samplerCorrect : Interactive.Refines layout.port .unit layout.good.service.evaluation.cache.lookup.unit.representation
    layout.scheme.rows.accumulation.cache.value.representation (fun _ => scalarSource) sampler
  scalarLaw : Subtype.val <$> scalarSource = ($ᵗ F : ProbComp F)
  samplerBudget : WeightedFull.Budget
  samplerTime : Interactive.TimeBound layout.port .unit layout.good.service.evaluation.cache.lookup.unit.representation sampler samplerBudget.time
  samplerWords : (sampler.lower layout.port).descriptionWords ≤ samplerBudget.words
  samplerSlots : Nat
  samplerNames : WordIO.NamesBound (sampler.lower layout.port) samplerSlots
  samplerFits : (sampler.lower layout.port).DescriptionFits
  samplerReserve : PairSampling.slots samplerSlots samplerSlots + 5 < 2 ^ wordBits
  goodAddresses : WeightedOracle.namesBudget good.slots samplerSlots good.slots good.slots +
    WeightedCallerHandler.codeBudget (base := base F J) (key := indexTy) (val := scalarTy) layout.good.service layout.good.terms layout.good.termCountFits layout.good.termStorageFits
      layout.randomBound layout.randomFits goodBounds.generator.words samplerBudget.words goodBounds.update.words
        (fun signing => (goodBounds.response signing).words) + 1 < 2 ^ wordBits
  badAddresses : WeightedOracle.namesBudget bad.slots (PairSampling.slots samplerSlots samplerSlots) bad.slots bad.slots +
    WeightedCallerHandler.codeBudget (base := base F J) (key := indexTy) (val := pairTy) layout.bad.service layout.bad.terms layout.bad.termCountFits layout.bad.termStorageFits
      layout.randomBound layout.randomFits badBounds.generator.words
      (PairSampling.codeBudget layout.scheme.rows.accumulation.cache.value layout.scheme.rows.accumulation.cache.value samplerBudget.words samplerBudget.words)
      badBounds.update.words (fun signing => (badBounds.response signing).words) + 1 < 2 ^ wordBits
  cacheRoom : max 1 layout.scheme.terms * (2 * queries.total + 1) ≤ layout.scheme.rows.accumulation.cache.capacityPred + 1
  hashRoom : queries.total ≤ layout.scheme.hashes
  signRoom : queries.total ≤ layout.scheme.signs
  generatorValid : layout.scheme.rows.point.valid generator
  keyGeneratorValid : layout.key.valid keyGenerator

variable {F G PK J M queries terms generator keyGenerator}
    (P : Parameters F G PK J M queries terms generator keyGenerator)

namespace Parameters
abbrev scalar := P.layout.scheme.rows.accumulation.cache.value
abbrev pairSlots := PairSampling.slots P.samplerSlots P.samplerSlots
abbrev pairTime := PairSampling.timeBudget P.scalar P.scalar P.samplerBudget.time P.samplerBudget.time
abbrev pairWords := PairSampling.codeBudget P.scalar P.scalar P.samplerBudget.words P.samplerBudget.words

def resampling : WeightedFull.Resampling (base := base F J) (key := indexTy) (val := pairTy) P.layout.bad P.layout.badSetup where
  preparation := P.layout.preparation
  compatible := P.layout.prepared_challenge
  scale := P.keyScale
  slots := P.keySlots
  reserve := P.keyReserve
  names := P.keyNames
  budget := P.keyBudget
  bounded := P.keyBound

def pairSampler := PairSampling.code P.scalar P.scalar P.layout.scheme.rows.accumulation.cache.wordFits
  P.layout.scheme.rows.accumulation.cache.pairValueFits P.layout.port P.sampler P.sampler
def pairSource := PairSampling.denote P.scalar P.scalar P.layout.scheme.rows.accumulation.cache.pairValueFits P.scalarSource P.scalarSource

def goodTime : Nat := 200 * P.layout.goodSetup.width +
  WeightedCallerProgram.timeBudget (base := base F J) (key := indexTy) (val := scalarTy) P.layout.good true P.layout.key.representation.encoding.words
    P.goodBounds.generator.time P.samplerBudget.time P.goodBounds.update.time (fun s => (P.goodBounds.response s).time)
    P.callerLimits.step.time P.callerLimits.initial.time queries.total P.goodBounds.extract.time P.goodBounds.sum.time

def badTime : Nat := WeightedBadSetup.timeBudget P.layout.preparation P.samplerBudget.time P.keyBudget.time +
  (200 * P.layout.badSetup.width +
    WeightedCallerProgram.timeBudget (base := base F J) (key := indexTy) (val := pairTy) P.layout.bad false P.layout.key.representation.encoding.words
      P.badBounds.generator.time P.pairTime P.badBounds.update.time (fun s => (P.badBounds.response s).time)
      P.callerLimits.step.time P.callerLimits.initial.time queries.total P.badBounds.extract.time P.badBounds.sum.time)

def goodWords : Nat := 700 * P.layout.goodSetup.width + 252 +
  WeightedCallerProgram.codeBudget (base := base F J) (key := indexTy) (val := scalarTy) P.layout.good true P.layout.key.representation.encoding.words
    P.goodBounds.generator.words P.samplerBudget.words P.goodBounds.update.words (fun s => (P.goodBounds.response s).words)
    P.callerLimits.step.words P.callerLimits.initial.words queries.total P.goodBounds.extract.words P.goodBounds.sum.words

def badWords : Nat := WeightedBadSetup.codeBudget P.layout.preparation P.samplerBudget.words P.keyBudget.words +
  (700 * P.layout.badSetup.width + 252 +
    WeightedCallerProgram.codeBudget (base := base F J) (key := indexTy) (val := pairTy) P.layout.bad false P.layout.key.representation.encoding.words
      P.badBounds.generator.words P.pairWords P.badBounds.update.words (fun s => (P.badBounds.response s).words)
      P.callerLimits.step.words P.callerLimits.initial.words queries.total P.badBounds.extract.words P.badBounds.sum.words) + 1

def goodNames : Nat := max 5 (max P.callerLimits.slots (max P.good.slots (max P.samplerSlots
  (WeightedExtractor.nameBudget P.good.slots P.samplerSlots P.good.slots P.good.slots P.good.slots))))
def badNames : Nat := max (max (max 3 P.samplerSlots) P.keySlots)
  (max 5 (max P.callerLimits.slots (max P.bad.slots (max P.pairSlots
    (WeightedExtractor.nameBudget P.bad.slots P.pairSlots P.bad.slots P.bad.slots P.bad.slots)))))
def goodMemory : Nat := 5 * P.goodWords + 4 * P.goodNames + 3 + P.layout.goodSetup.challenge.representation.encoding.words + P.goodTime
def badMemory : Nat := 5 * P.badWords + 4 * P.badNames + 3 + P.layout.goodSetup.challenge.representation.encoding.words + P.badTime
def solverCode : Nat := max P.goodWords P.badWords
def solverMemory : Nat := max P.goodMemory P.badMemory

def within (time : Nat) (solver : AlgebraicGroupModel.DLog11Adversary F G PK) : Prop :=
  dlogWithin P.layout.port P.layout.goodSetup.challenge P.scalar generator keyGenerator P.solverCode P.solverMemory time solver
noncomputable def dlogBound (time : Nat) : ENNReal :=
  dlogSuccessBound P.layout.port P.layout.goodSetup.challenge P.scalar generator keyGenerator P.solverCode P.solverMemory time
end Parameters

structure AlgebraicAdversary where
  source : Model.DirectAGM.Adversary F J M G PK
  caller : WeightedFull.SharedCaller (base := base F J) (key := indexTy) (scalar := scalarTy) P.layout
  invariant : WeightedFull.Invariant (base := base F J) (key := indexTy) (val := scalarTy) P.layout.good P.layout.goodSetup caller queries.total
  correspondence : WeightedFull.Correspondence (base := base F J) (key := indexTy) (val := scalarTy) P.layout.good P.layout.goodSetup caller queries.total invariant (Equiv.refl J)
  source_eq : ∀ pk : P.layout.key.Value,
    (fun answer => WeightedCallerProgram.output answer.val) <$> correspondence.source pk.val =
      (Model.DirectAGM.ProofView.adversary generator source).main pk.val
  localTime : ∀ value, caller.continuation.time value ≤ P.callerLimits.step.time
  initialTime : ∀ value, caller.initialCode.time value ≤ P.callerLimits.initial.time
  localWords : descriptionWords caller.continuation.code ≤ P.callerLimits.step.words
  initialWords : descriptionWords caller.initialCode.code ≤ P.callerLimits.initial.words
  localNames : NamesAccounted caller.continuation.code P.callerLimits.slots
  initialNames : NamesAccounted caller.initialCode.code P.callerLimits.slots
  randomQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput generator pk))
    (fun i => BLS.queryKind i.value.data = 0) queries.random
  hashQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput generator pk))
    (fun i => BLS.queryKind i.value.data = 1) queries.hash
  signingQueries : ∀ pk, IsQueryBoundP (source.main (Model.LazyAGM.Interactive.initialInput generator pk))
    (fun i => BLS.queryKind i.value.data = 2) queries.sign

def AlgebraicAdversary.bounds (A : AlgebraicAdversary P) :
    WeightedFull.Caller.Bounds (base := base F J) (key := indexTy) (val := scalarTy) P.layout.good P.layout.goodSetup A.caller where
  step := P.callerLimits.step
  initial := P.callerLimits.initial
  slots := P.callerLimits.slots
  localTime := A.localTime
  initialTime := A.initialTime
  localWords := A.localWords
  initialWords := A.initialWords
  localNames := A.localNames
  initialNames := A.initialNames

def AlgebraicAdversary.proofView (A : AlgebraicAdversary P) := Model.DirectAGM.ProofView.adversary generator A.source
end Signatures.Runtime.WeightedCaliper
