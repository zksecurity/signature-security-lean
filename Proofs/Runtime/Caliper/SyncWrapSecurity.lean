import Proofs.Runtime.Caliper.SyncWrapParameters
import Proofs.BLS.LazyAGMSecurity
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling
import VCVio.OracleComp.Constructions.SampleableType.MeasureCompatibility

/-! The four complete Caliper solvers for synchronized PS and their certificates. For each
scheme the attacker's inner caller is wrapped (`SyncWrap`), the outer caller is run by the keyed
weighted programs, and the executed program is, at the curve's generators, the corresponding
solver of `WrappedSecurity.lean`: as a program for the good branches, in distribution for the
bad branches, whose outer sample `κ` and known key are drawn in the other order. -/
namespace Signatures.Runtime.SyncWrapCaliper
open Caliper OracleComp OracleSpec CaliperBackend BoundedSource CaliperBackend.SyncWrap WeightedFull
open Signatures.Runtime.WeightedCaliper (base scalarTy indexTy pairTy QueryAllowance primitives comparison comparison_correct)
open Model.LazyAGM Model.LazyAGM.WeightedReduction SynchronizedPS.Wrapped

set_option linter.unusedSectionVars false

variable {F G₁ G₂ Period : Type} [Field F] [SampleableType F] [DecidableEq Period]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
  {queries : QueryAllowance} {generator : G₁} {keyGenerator : G₂}
  (P : Parameters F G₁ G₂ Period queries generator keyGenerator)

/-- Distributions on the scalar field, as in `dlog11Advantage_congr`. -/
local instance : MeasurableSpace F := ⊤

namespace Parameters

abbrev shape := P.frame.shape
abbrev core := P.shape.core
abbrev wrapper := P.frame.wrapper
abbrev outer := P.frame.outer
abbrev scalar : Layout P.wordBits F := P.shape.scalar

/-! ## The sampler -/

theorem scalar_valid (s : F) : P.scalar.valid s := by
  have reached : s ∈ support (Subtype.val <$> P.scalarSource) := by
    rw [P.scalarLaw]
    exact mem_support_uniformSample F
  rw [support_map, Set.mem_image] at reached
  obtain ⟨represented, _, equal⟩ := reached
  exact equal ▸ represented.property

theorem key_valid (s : F) : P.shape.keyG₂.valid (s • keyGenerator) :=
  P.keyScale.preserves (s, keyGenerator) ⟨P.scalar_valid s, P.keyGeneratorValid⟩

theorem challenge_valid (s : F) :
    P.shape.keyed.challenge.valid ((generator, s • generator), (keyGenerator, s • keyGenerator)) := by
  have point := (P.good₁.routines.response false).preserves (s, (generator, generator))
    ⟨P.scalar_valid s, P.generatorValid, P.generatorValid⟩
  rw [P.good₁.response] at point
  exact ⟨⟨P.generatorValid, point⟩, P.keyGeneratorValid, P.key_valid s⟩

abbrev pairSlots := PairSampling.slots P.samplerSlots P.samplerSlots
abbrev pairTime := PairSampling.timeBudget P.scalar P.scalar P.samplerBudget.time P.samplerBudget.time
abbrev pairWords := PairSampling.codeBudget P.scalar P.scalar P.samplerBudget.words P.samplerBudget.words
def pairSampler := PairSampling.code P.scalar P.scalar P.shape.scheme.rows.accumulation.cache.wordFits
  P.shape.scheme.rows.accumulation.cache.pairValueFits P.outer.port P.sampler P.sampler
def pairSource := PairSampling.denote P.scalar P.scalar P.shape.scheme.rows.accumulation.cache.pairValueFits P.scalarSource P.scalarSource

theorem pair_correct : Interactive.Refines P.outer.port .unit
    P.outer.bad.service.evaluation.cache.lookup.unit.representation
    P.outer.bad.service.evaluation.cache.value.representation (fun _ => P.pairSource) P.pairSampler :=
  PairSampling.refines (hw := P.shape.scheme.rows.accumulation.cache.wordFits)
    (fits := P.shape.scheme.rows.accumulation.cache.pairValueFits) P.samplerCorrect P.samplerCorrect
theorem pair_uniform : Subtype.val <$> P.pairSource = ($ᵗ (F × F) : ProbComp (F × F)) :=
  PairSampling.uniform P.scalar P.scalar P.shape.scheme.rows.accumulation.cache.pairValueFits P.scalarSource P.scalarSource P.scalarLaw P.scalarLaw
theorem pair_time : Interactive.TimeBound P.outer.port .unit
    P.outer.bad.service.evaluation.cache.lookup.unit.representation P.pairSampler P.pairTime :=
  PairSampling.time_bound (hw := P.shape.scheme.rows.accumulation.cache.wordFits)
    (fits := P.shape.scheme.rows.accumulation.cache.pairValueFits) P.samplerCorrect P.samplerCorrect P.samplerTime P.samplerTime
theorem pair_words : (P.pairSampler.lower P.outer.port).descriptionWords ≤ P.pairWords :=
  PairSampling.code_bound P.scalar P.scalar P.shape.scheme.rows.accumulation.cache.wordFits
    P.shape.scheme.rows.accumulation.cache.pairValueFits P.outer.port P.sampler P.sampler P.samplerWords P.samplerWords
theorem pair_names : WordIO.NamesBound (P.pairSampler.lower P.outer.port) P.pairSlots :=
  PairSampling.names P.scalar P.scalar P.shape.scheme.rows.accumulation.cache.wordFits
    P.shape.scheme.rows.accumulation.cache.pairValueFits P.outer.port P.sampler P.sampler P.samplerNames P.samplerNames
theorem scalar_reserve : P.samplerSlots + 5 < 2 ^ P.wordBits := by
  have bound := P.samplerReserve
  unfold PairSampling.slots at bound
  omega
theorem pair_fits : (P.pairSampler.lower P.outer.port).DescriptionFits :=
  PairSampling.descriptionFits P.scalar P.scalar P.shape.scheme.rows.accumulation.cache.wordFits
    P.shape.scheme.rows.accumulation.cache.pairValueFits P.outer.port P.sampler P.sampler
      P.samplerFits P.samplerFits P.samplerNames (by have := P.scalar_reserve; omega)

/-! ## The outer caller of one scheme -/

section Side
variable {corrSpec finSpec : F → Period × F → F} (side : WrapSide F G₁ G₂ Period P.core corrSpec finSpec)

abbrev finishImpl := P.wrapper.finish P.outLe side.finish
abbrev finishTime : Nat := P.wrapper.finishTime P.outLe side.finish
abbrev finishWords : Nat := P.wrapper.finishWords P.outLe side.finish
abbrev finishSlots : Nat := Wrapper.slotsAll side.finish
/-- The unit of the wrapper caller's budgets. -/
def unitT : Nat := P.core.bound + side.routines.time + P.core.snocTime + P.callerLimits.step.time + P.callerLimits.initial.time + P.finishTime side + 1
def unitW : Nat := P.core.bound + side.routines.words + P.core.snocWords + P.callerLimits.step.words + P.callerLimits.initial.words + P.finishWords side + 1
def outerSlots : Nat := side.routines.slots + P.callerLimits.slots + P.finishSlots side + 3
/-- The outer caller's allowances. -/
def outerLimits : Caller.Limits :=
  ⟨⟨3000000 * P.unitT side, 3000000 * P.unitW side⟩, ⟨900000 * P.unitT side, 900000 * P.unitW side⟩, P.outerSlots side⟩
end Side

theorem reserve₁ : P.outerSlots P.wrap₁ + 3000000 * P.unitW P.wrap₁ + 2 < 2 ^ P.wordBits := P.wrapReserve₁
theorem reserve₂ : P.outerSlots P.wrap₂ + 3000000 * P.unitW P.wrap₂ + 2 < 2 ^ P.wordBits := P.wrapReserve₂
theorem fuelRoom : queries.total ≤ P.frame.shape.core.slotCap := by
  have := P.slotRoom
  unfold outerFuel at this
  omega
theorem roomOut : outerFuel queries + 1 ≤ P.frame.shape.core.slotCap := P.slotRoom

end Parameters

/-! ## The attacker's certificate -/

/-- An algebraic attacker with a Caliper caller for the inner interface: the caller corresponds
to the attacker's proof view at the model's generator, within the model's local budgets and
signing allowance. -/
structure AlgebraicAdversary where
  source : SynchronizedPS.Reduction.Adversary F Period G₁ G₂
  caller : SharedCaller (base := base F Period) (key := indexTy) (scalar := scalarTy) P.core.inner
  invariant : Invariant (base := base F Period) (key := indexTy) (val := scalarTy) P.core.inner.good P.core.inner.goodSetup caller queries.total
  correspondence : Correspondence (base := base F Period) (key := indexTy) (val := scalarTy) P.core.inner.good P.core.inner.goodSetup caller
    queries.total invariant (Equiv.refl Period)
  source_eq : ∀ pk : P.core.inner.key.Value,
    ((fun answer => WeightedCallerProgram.output answer.val) <$> correspondence.source pk.val) =
      (SynchronizedPS.Proofs.view source generator).main pk.val
  localTime : ∀ value, caller.continuation.time value ≤ P.callerLimits.step.time
  initialTime : ∀ value, caller.initialCode.time value ≤ P.callerLimits.initial.time
  localWords : descriptionWords caller.continuation.code ≤ P.callerLimits.step.words
  initialWords : descriptionWords caller.initialCode.code ≤ P.callerLimits.initial.words
  localNames : NamesAccounted caller.continuation.code P.callerLimits.slots
  initialNames : NamesAccounted caller.initialCode.code P.callerLimits.slots
  signingQueries : ∀ pk, IsQueryBoundP (correspondence.source pk) isSign queries.sign

namespace AlgebraicAdversary
variable {P} (A : AlgebraicAdversary P)

def bounds : Caller.Bounds (base := base F Period) (key := indexTy) (val := scalarTy) P.core.inner.good P.core.inner.goodSetup A.caller where
  step := P.callerLimits.step
  initial := P.callerLimits.initial
  slots := P.callerLimits.slots
  localTime := A.localTime
  initialTime := A.initialTime
  localWords := A.localWords
  initialWords := A.initialWords
  localNames := A.localNames
  initialNames := A.initialNames

theorem callerReserve : A.caller.continuation.code.memBound + 50 < 2 ^ P.wordBits := by
  have names := A.localNames.buffers
  have words := A.localWords
  have room := P.callerReserve
  omega
theorem initialReserve : A.caller.initialCode.code.memBound + 50 < 2 ^ P.wordBits := by
  have names := A.initialNames.buffers
  have words := A.initialWords
  have room := P.initialReserve
  omega
section Side
variable {corrSpec finSpec : F → Period × F → F} (side : WrapSide F G₁ G₂ Period P.core corrSpec finSpec)
  (reserve : P.outerSlots side + 3000000 * P.unitW side + 2 < 2 ^ P.wordBits)

/-- The wrapper around the attacker's caller, as the outer caller. -/
def outerCaller : SharedCaller (base := base F Period) (key := indexTy) (scalar := scalarTy) P.outer :=
  P.wrapper.toCaller side.routines A.caller P.outLe (P.finishImpl side) A.callerReserve A.initialReserve A.bounds
    (P.finishTime side) (P.finishWords side) (P.finishSlots side) (P.wrapper.finish_boundedBy P.outLe side.finish)
    (P.wrapper.finish_names P.outLe side.finish) reserve
def outerBounds : Caller.Bounds (base := base F Period) (key := indexTy) (val := scalarTy) P.outer.good P.outer.goodSetup (A.outerCaller side reserve) :=
  P.wrapper.bounds side.routines A.caller P.outLe (P.finishImpl side) A.callerReserve A.initialReserve A.bounds
    (P.finishTime side) (P.finishWords side) (P.finishSlots side) (P.wrapper.finish_boundedBy P.outLe side.finish)
    (P.wrapper.finish_names P.outLe side.finish) reserve
def outerInvariant : Invariant (base := base F Period) (key := indexTy) (val := scalarTy) P.outer.good P.outer.goodSetup (A.outerCaller side reserve) (outerFuel queries) :=
  P.wrapper.invariant' side.routines A.caller P.outLe (P.finishImpl side) A.callerReserve A.initialReserve P.messageTotal side.fmaLaw
    queries.total A.invariant A.correspondence (outerFuel queries) P.roomOut A.bounds
    (P.finishTime side) (P.finishWords side) (P.finishSlots side) (P.wrapper.finish_boundedBy P.outLe side.finish)
    (P.wrapper.finish_names P.outLe side.finish) reserve
noncomputable def outerCorrespondence : Correspondence (base := base F Period) (key := indexTy) (val := scalarTy) P.outer.good P.outer.goodSetup
    (A.outerCaller side reserve) (outerFuel queries) (A.outerInvariant side reserve) (Equiv.refl Period) :=
  P.wrapper.correspondence side.routines A.caller P.outLe (P.finishImpl side) A.callerReserve A.initialReserve P.messageTotal side.hashOfLaw side.fmaLaw
    queries.total A.invariant A.correspondence (outerFuel queries) P.roomOut A.bounds
    (P.finishTime side) (P.finishWords side) (P.finishSlots side) (P.wrapper.finish_boundedBy P.outLe side.finish)
    (P.wrapper.finish_names P.outLe side.finish) reserve queries.sign A.signingQueries P.fuelRoom le_rfl
/-- The wrapped attacker as the weighted adversary the outer programs run. -/
noncomputable def outerAdversary : Adversary F Period (Period × F) G₁ ((G₂ × G₂) × F) :=
  P.wrapper.outerAdversary side.routines A.caller P.outLe side.finish P.messageTotal queries.total A.invariant A.correspondence
theorem outer_same : ∀ pk : P.outer.goodSetup.key.Value,
    (fun answer => WeightedCallerProgram.output answer.val) <$> (A.outerCorrespondence side reserve).source pk.val =
      (A.outerAdversary side).main pk.val := fun _ => rfl
end Side

end AlgebraicAdversary

/-! ## Budgets -/

namespace Parameters
section Budgets
variable {corrSpec finSpec : F → Period × F → F} (side : WrapSide F G₁ G₂ Period P.core corrSpec finSpec)
  {terms : Period × F → List (Period × F)}
  (gs : GoodSide F G₁ Period P.outer.good terms P.samplerBudget.words P.samplerSlots)
  (bs : BadSide F G₁ Period P.outer.bad terms P.pairWords P.pairSlots)
  (postTime postWords postSlots : Nat)

def goodCallerWords : Nat := 700 * P.outer.goodSetup.width + 252 +
  WeightedCallerProgram.codeBudget (base := base F Period) (key := indexTy) (val := scalarTy) P.outer.good true
    P.outer.goodSetup.key.representation.encoding.words gs.bounds.generator.words P.samplerBudget.words gs.bounds.update.words
    (fun signing => (gs.bounds.response signing).words) (P.outerLimits side).step.words (P.outerLimits side).initial.words
    (outerFuel queries) gs.bounds.extract.words gs.bounds.sum.words
def goodCallerTime : Nat := 200 * P.outer.goodSetup.width +
  WeightedCallerProgram.timeBudget (base := base F Period) (key := indexTy) (val := scalarTy) P.outer.good true
    P.outer.goodSetup.key.representation.encoding.words gs.bounds.generator.time P.samplerBudget.time gs.bounds.update.time
    (fun signing => (gs.bounds.response signing).time) (P.outerLimits side).step.time (P.outerLimits side).initial.time
    (outerFuel queries) gs.bounds.extract.time gs.bounds.sum.time
def goodNames : Nat := max 5 (max (P.outerLimits side).slots (max gs.routines.slots (max P.samplerSlots
  (WeightedExtractor.nameBudget gs.routines.slots P.samplerSlots gs.routines.slots gs.routines.slots gs.routines.slots))))
def goodWords : Nat := KeyedSetup.codeBudget P.shape.keyed P.samplerBudget.words P.keyBudget.words + postWords + 1 + P.goodCallerWords side gs + 1
def goodTime : Nat := KeyedSetup.timeBudget P.shape.keyed P.samplerBudget.time P.keyBudget.time + postTime + P.goodCallerTime side gs
def goodMemory : Nat := 5 * P.goodWords side gs postWords +
  4 * max (max (max (max 3 P.samplerSlots) P.keySlots) postSlots) (P.goodNames side gs) + 3 +
  P.shape.keyed.challenge.representation.encoding.words + P.goodTime side gs postTime

def badCallerWords : Nat := 700 * P.outer.badSetup.width + 252 +
  WeightedCallerProgram.codeBudget (base := base F Period) (key := indexTy) (val := pairTy) P.outer.bad false
    P.outer.badSetup.key.representation.encoding.words bs.bounds.generator.words P.pairWords bs.bounds.update.words
    (fun signing => (bs.bounds.response signing).words) (P.outerLimits side).step.words (P.outerLimits side).initial.words
    (outerFuel queries) bs.bounds.extract.words bs.bounds.sum.words
def badCallerTime : Nat := 200 * P.outer.badSetup.width +
  WeightedCallerProgram.timeBudget (base := base F Period) (key := indexTy) (val := pairTy) P.outer.bad false
    P.outer.badSetup.key.representation.encoding.words bs.bounds.generator.time P.pairTime bs.bounds.update.time
    (fun signing => (bs.bounds.response signing).time) (P.outerLimits side).step.time (P.outerLimits side).initial.time
    (outerFuel queries) bs.bounds.extract.time bs.bounds.sum.time
def badNames : Nat := max 5 (max (P.outerLimits side).slots (max bs.routines.slots (max P.pairSlots
  (WeightedExtractor.nameBudget bs.routines.slots P.pairSlots bs.routines.slots bs.routines.slots bs.routines.slots))))
def badWords : Nat := WeightedBadSetup.codeBudget P.shape.preparation P.samplerBudget.words P.keyBudget.words +
  KeyedSetup.codeBudget P.shape.badKeyed P.samplerBudget.words P.keyBudget.words + 1 + postWords + 1 + P.badCallerWords side bs + 1
def badTime : Nat := WeightedBadSetup.timeBudget P.shape.preparation P.samplerBudget.time P.keyBudget.time +
  KeyedSetup.timeBudget P.shape.badKeyed P.samplerBudget.time P.keyBudget.time + postTime + P.badCallerTime side bs
def badMemory : Nat := 5 * P.badWords side bs postWords +
  4 * max (max (max (max (max 3 P.samplerSlots) P.keySlots) (max (max 3 P.samplerSlots) P.keySlots)) postSlots) (P.badNames side bs) + 3 +
  P.shape.preparation.challenge.representation.encoding.words + P.badTime side bs postTime
end Budgets

/-- Scheme₁ keeps the keyed challenge `((pk, k • g₂), k)`; scheme₂ swaps the key pair. -/
def postGood₁ : Preparation.Stage P.outer.port P.outer.goodSetup.challenge P.outer.goodSetup.challenge := KeyedSetup.keepStage P.shape.keyed P.outer.port
def postBad₁ : Preparation.Stage P.outer.port P.outer.badSetup.challenge P.outer.badSetup.challenge := KeyedSetup.keepStage P.shape.badKeyed P.outer.port
def postGood₂ : Preparation.Stage P.outer.port P.outer.goodSetup.challenge P.outer.goodSetup.challenge := KeyedSetup.swapStage P.shape.keyed P.outer.port
def postBad₂ : Preparation.Stage P.outer.port P.outer.badSetup.challenge P.outer.badSetup.challenge := KeyedSetup.swapStage P.shape.badKeyed P.outer.port

def goodWords₁ : Nat := P.goodWords P.wrap₁ P.good₁ P.postGood₁.words
def goodTime₁ : Nat := P.goodTime P.wrap₁ P.good₁ P.postGood₁.time
def goodMemory₁ : Nat := P.goodMemory P.wrap₁ P.good₁ P.postGood₁.time P.postGood₁.words P.postGood₁.slots
def badWords₁ : Nat := P.badWords P.wrap₁ P.bad₁ P.postBad₁.words
def badTime₁ : Nat := P.badTime P.wrap₁ P.bad₁ P.postBad₁.time
def badMemory₁ : Nat := P.badMemory P.wrap₁ P.bad₁ P.postBad₁.time P.postBad₁.words P.postBad₁.slots
def goodWords₂ : Nat := P.goodWords P.wrap₂ P.good₂ P.postGood₂.words
def goodTime₂ : Nat := P.goodTime P.wrap₂ P.good₂ P.postGood₂.time
def goodMemory₂ : Nat := P.goodMemory P.wrap₂ P.good₂ P.postGood₂.time P.postGood₂.words P.postGood₂.slots
def badWords₂ : Nat := P.badWords P.wrap₂ P.bad₂ P.postBad₂.words
def badTime₂ : Nat := P.badTime P.wrap₂ P.bad₂ P.postBad₂.time
def badMemory₂ : Nat := P.badMemory P.wrap₂ P.bad₂ P.postBad₂.time P.postBad₂.words P.postBad₂.slots

def solverCode : Nat := max (max P.goodWords₁ P.badWords₁) (max P.goodWords₂ P.badWords₂)
def solverMemory : Nat := max (max P.goodMemory₁ P.badMemory₁) (max P.goodMemory₂ P.badMemory₂)

def within (time : Nat) (solver : AlgebraicGroupModel.DLog11Adversary F G₁ G₂) : Prop :=
  dlogWithin P.outer.port P.shape.challenge P.outer.good.extraction.scalar generator keyGenerator P.solverCode P.solverMemory time solver
noncomputable def dlogBound (time : Nat) : ENNReal :=
  dlogSuccessBound P.outer.port P.shape.challenge P.outer.good.extraction.scalar generator keyGenerator P.solverCode P.solverMemory time
end Parameters

/-! ## The certificates -/

namespace AlgebraicAdversary
variable {P} (A : AlgebraicAdversary P)
variable {corrSpec finSpec : F → Period × F → F} (side : WrapSide F G₁ G₂ Period P.core corrSpec finSpec)
  (reserve : P.outerSlots side + 3000000 * P.unitW side + 2 < 2 ^ P.wordBits)
  {terms : Period × F → List (Period × F)}

section Good
variable (gs : GoodSide F G₁ Period P.outer.good terms P.samplerBudget.words P.samplerSlots)
  (post : Preparation.Stage P.outer.port P.outer.goodSetup.challenge P.outer.goodSetup.challenge)
  (postFn : (G₁ × G₁) × (((G₂ × G₂) × F) × ((G₂ × G₂) × F)) → (G₁ × G₁) × (((G₂ × G₂) × F) × ((G₂ × G₂) × F)))
  (postLaw : ∀ value, Subtype.val <$> post.source value = pure (postFn value.val))

/-- The executed good solver: draw the known key, run the keyed weighted good program. -/
noncomputable def caliperGood : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g X g₂ Z₂ =>
  P.scalarSource >>= fun s =>
    let keyedValue := postFn ((g, X), (((Z₂, s.val • g₂), s.val), ((Z₂, s.val • g₂), s.val)))
    goodReductionList terms (A.outerAdversary side) keyedValue.1.1 keyedValue.1.2 keyedValue.2.1 keyedValue.2.2

theorem termsEqual_good : ∀ message, gs.routines.generate message = (terms message).map (Prod.map (Equiv.refl Period) id) := by
  intro message
  simpa using congrFun gs.terms_eq message

include reserve postLaw in
theorem caliperGood_within :
    dlogWithin P.outer.port P.shape.keyed.challenge P.outer.good.extraction.scalar generator keyGenerator
      (P.goodWords side gs post.words) (P.goodMemory side gs post.time post.words post.slots) (P.goodTime side gs post.time)
      (A.caliperGood (terms := terms) side postFn) :=
  WeightedFull.keyed_good_dlogWithin (base := base F Period) (key := indexTy) (val := scalarTy)
    (layout := P.outer.good) (setup := P.outer.goodSetup) (routines := gs.routines) (P := primitives F Period)
    (comparison := comparison) (correct := comparison_correct F Period) (caller := A.outerCaller side reserve) (fuel := outerFuel queries)
    (source := P.scalarSource) (coefficientLaw := gs.coefficient) (combineLaw := gs.combine) (zeroLaw := rfl) (uniform := P.scalarLaw)
    (respondLaw := gs.response) (calculateLaw := gs.extract) (numeratorLaw := gs.sum) (invariant := A.outerInvariant side reserve)
    (cacheRoom := P.cacheRoom) (hashRoom := P.hashRoom) (signRoom := P.signRoom) (keys := Equiv.refl Period) (terms := terms)
    (termsEqual := termsEqual_good gs) (witness := A.outerCorrespondence side reserve) (adversary := A.outerAdversary side)
    (same := A.outer_same side reserve) (bound := gs.bounds) (localBound := A.outerBounds side reserve)
    (draw := P.sampler) (drawCorrect := P.samplerCorrect) (drawTimeBound := P.samplerTime) (drawWordsBound := P.samplerWords)
    (drawNames := P.samplerNames) (drawFits := P.samplerFits) (drawReserve := P.scalar_reserve) (handlerReserve := gs.addresses)
    (generator := generator) (keyGenerator := keyGenerator) (keyed := P.shape.keyed) (compatible := P.frame.compatible)
    (scale := P.keyScale) (scaleBuffers := P.keyBuffers) (scaleReserve := P.keyReserve) (scaleBound := P.keyBound) (scaleNames := P.keyNames)
    (keyDraw := P.sampler) (keySource := P.scalarSource) (keyCorrect := P.samplerCorrect) (keyTimeBound := P.samplerTime)
    (keyWordsBound := P.samplerWords) (keyNames := P.samplerNames) (keyFits := P.samplerFits)
    (keyReserve := by have := P.scalar_reserve; omega) (challengeValid := P.challenge_valid) (post := post) (postFn := postFn) (postLaw := postLaw)

variable (correction : F → Period × F → F) (final : F → SynchronizedPS.Forgery F Period → F) (keysOf : F → G₂ → G₂ → G₂ × G₂)
  (postEq : ∀ g X g₂ Z₂ s, postFn ((g, X), (((Z₂, s • g₂), s), ((Z₂, s • g₂), s))) = ((g, X), ((keysOf s g₂ Z₂, s), (keysOf s g₂ Z₂, s))))
  (corrLaw : ∀ (d : P.core.scalar.Value) (m : P.core.message.Value), (side.routines.corrFn (d, m)).val = correction d.val m.val)
  (finLaw : ∀ (d : P.core.scalar.Value) (m : Period × F), side.finish.negFn (side.finish.finFn (d.val, m)) = -(final d.val m))
  (keysValid : ∀ (s : P.scalar.Value) (α : F), P.core.inner.key.valid (keysOf s.val keyGenerator (α • keyGenerator)))

include postEq corrLaw finLaw keysValid in
/-- At the curve's generators, the wrapped-attacker good solver is the executed good solver. -/
theorem good_eq (X : G₁) (α : F) :
    (($ᵗ F : ProbComp F) >>= fun y =>
      goodReductionList terms (wrap (correction y) (final y) (keysOf y keyGenerator) (SynchronizedPS.Proofs.view A.source generator)) generator X keyGenerator (α • keyGenerator)) =
    A.caliperGood (terms := terms) side postFn generator X keyGenerator (α • keyGenerator) := by
  unfold caliperGood
  rw [← P.scalarLaw, bind_map_left]
  refine bind_congr fun s => ?_
  show goodReductionList terms _ generator X keyGenerator (α • keyGenerator) =
    goodReductionList terms _ (postFn _).1.1 (postFn _).1.2 (postFn _).2.1 (postFn _).2.2
  rw [postEq]
  unfold goodReductionList AlgebraicAdversary.outerAdversary
  rw [goodProgram_congr terms generator X (Wrapper.outerAdversary_main_eq side.routines A.caller P.wrapper P.outLe side.finish P.messageTotal
    queries.total A.invariant A.correspondence (SynchronizedPS.Proofs.view A.source generator) A.source_eq correction final (keysOf s.val keyGenerator) corrLaw finLaw side.mulLaw
    P.fuelRoom ⟨keysOf s.val keyGenerator (α • keyGenerator), keysValid s α⟩ s (α • keyGenerator) rfl).symm]

include postEq corrLaw finLaw keysValid in
/-- At the curve's generators the wrapped-attacker good solver and the executed one have the same advantage. -/
theorem good_advantage_eq :
    Model.dlog11Advantage generator keyGenerator (fun g X g₂ Z₂ => ($ᵗ F : ProbComp F) >>= fun y =>
      goodReductionList terms (wrap (correction y) (final y) (keysOf y g₂) (SynchronizedPS.Proofs.view A.source generator)) g X g₂ Z₂) =
    Model.dlog11Advantage generator keyGenerator (A.caliperGood (terms := terms) side postFn) :=
  BLS.LazyAGM.Reduction.dlog11Advantage_congr generator keyGenerator _ (A.caliperGood (terms := terms) side postFn)
    (fun α => congrArg _ (A.good_eq side postFn correction final keysOf postEq corrLaw finLaw keysValid (α • generator) α))

include postLaw reserve in
theorem caliperGood_within' (codeLe : P.goodWords side gs post.words ≤ P.solverCode)
    (memoryLe : P.goodMemory side gs post.time post.words post.slots ≤ P.solverMemory) :
    P.within (P.goodTime side gs post.time) (A.caliperGood (terms := terms) side postFn) :=
  (A.caliperGood_within side reserve gs post postFn postLaw).mono codeLe memoryLe le_rfl

include postEq corrLaw finLaw keysValid postLaw reserve in
theorem good_advantage (codeLe : P.goodWords side gs post.words ≤ P.solverCode)
    (memoryLe : P.goodMemory side gs post.time post.words post.slots ≤ P.solverMemory) :
    Model.dlog11Advantage generator keyGenerator (fun g X g₂ Z₂ => ($ᵗ F : ProbComp F) >>= fun y =>
      goodReductionList terms (wrap (correction y) (final y) (keysOf y g₂) (SynchronizedPS.Proofs.view A.source generator)) g X g₂ Z₂) ≤
    P.dlogBound (P.goodTime side gs post.time) :=
  (A.good_advantage_eq side postFn correction final keysOf postEq corrLaw finLaw keysValid).trans_le
    (Model.le_advantageBound _ _ _ (A.caliperGood_within' side reserve gs post postFn postLaw codeLe memoryLe))
end Good

section Bad
variable (bs : BadSide F G₁ Period P.outer.bad terms P.pairWords P.pairSlots)
  (post : Preparation.Stage P.outer.port P.outer.badSetup.challenge P.outer.badSetup.challenge)
  (postFn : (F × (G₁ × G₁)) × (((G₂ × G₂) × F) × ((G₂ × G₂) × F)) → (F × (G₁ × G₁)) × (((G₂ × G₂) × F) × ((G₂ × G₂) × F)))
  (postLaw : ∀ value, Subtype.val <$> post.source value = pure (postFn value.val))

/-- The executed bad solver: resample the key, draw the known key, run the keyed weighted bad program. -/
noncomputable def caliperBad : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := fun g X g₂ _ =>
  P.scalarSource >>= fun kappa => P.scalarSource >>= fun s =>
    let keyedValue := postFn ((kappa.val, (g, X)), (((kappa.val • g₂, s.val • g₂), s.val), ((kappa.val • g₂, s.val • g₂), s.val)))
    (simulateQ BLS.LazyAGM.Reduction.privateListOracle
      (badProgram terms keyedValue.1.2.1 keyedValue.1.2.2 keyedValue.2.2 keyedValue.1.1 (A.outerAdversary side))).run' []

theorem termsEqual_bad : ∀ message, bs.routines.generate message = (terms message).map (Prod.map (Equiv.refl Period) id) := by
  intro message
  simpa using congrFun bs.terms_eq message

include reserve postLaw in
theorem caliperBad_within :
    dlogWithin P.outer.port P.shape.preparation.challenge P.outer.good.extraction.scalar generator keyGenerator
      (P.badWords side bs post.words) (P.badMemory side bs post.time post.words post.slots) (P.badTime side bs post.time)
      (A.caliperBad (terms := terms) side postFn) :=
  WeightedFull.keyed_bad_dlogWithin (base := base F Period) (key := indexTy) (scalar := scalarTy)
    (layout := P.outer.bad) (setup := P.outer.badSetup) (routines := bs.routines) (P := primitives F Period)
    (comparison := comparison) (correct := comparison_correct F Period)
    (caller := SharedCaller.bad (base := base F Period) (key := indexTy) (scalar := scalarTy) P.outer (A.outerCaller side reserve))
    (fuel := outerFuel queries) (source := P.pairSource) (coefficientLaw := bs.coefficient) (combineLaw := bs.combine) (zeroLaw := rfl)
    (uniform := P.pair_uniform) (respondLaw := bs.response) (calculateLaw := bs.extract)
    (invariant := SharedCaller.badInvariant (base := base F Period) (key := indexTy) (scalar := scalarTy) P.outer (A.outerCaller side reserve)
      (outerFuel queries) (A.outerInvariant side reserve))
    (cacheRoom := P.cacheRoom) (hashRoom := P.hashRoom) (signRoom := P.signRoom) (keys := Equiv.refl Period) (terms := terms)
    (termsEqual := termsEqual_bad bs)
    (witness := SharedCaller.badCorrespondence (base := base F Period) (key := indexTy) (scalar := scalarTy) P.outer (A.outerCaller side reserve)
      (outerFuel queries) (A.outerInvariant side reserve) (Equiv.refl Period) (A.outerCorrespondence side reserve))
    (adversary := A.outerAdversary side) (same := A.outer_same side reserve) (bound := bs.bounds)
    (localBound := SharedCaller.badBounds (base := base F Period) (key := indexTy) (scalar := scalarTy) P.outer (A.outerCaller side reserve)
      (A.outerBounds side reserve))
    (draw := P.pairSampler) (drawCorrect := P.pair_correct) (drawTimeBound := P.pair_time) (drawWordsBound := P.pair_words)
    (drawNames := P.pair_names) (drawFits := P.pair_fits) (drawReserve := P.samplerReserve) (handlerReserve := bs.addresses)
    (generator := generator) (keyGenerator := keyGenerator)
    (preparation := P.shape.preparation) (resample := P.keyScale) (resampleBuffers := P.keyBuffers) (resampleReserve := P.keyReserve)
    (resampleBound := P.keyBound) (resampleNames := P.keyNames)
    (outerDraw := P.sampler) (outerSource := P.scalarSource) (outerCorrect := P.samplerCorrect) (outerTimeBound := P.samplerTime)
    (outerWordsBound := P.samplerWords) (outerNames := P.samplerNames) (outerFits := P.samplerFits)
    (outerReserve := by have := P.scalar_reserve; omega)
    (keyed := P.shape.badKeyed) (prepared := P.shape.prepared) (compatible := P.frame.badCompatible)
    (scale := P.keyScale) (scaleBuffers := P.keyBuffers) (scaleReserve := P.keyReserve) (scaleBound := P.keyBound) (scaleNames := P.keyNames)
    (keyDraw := P.sampler) (keySource := P.scalarSource) (keyCorrect := P.samplerCorrect) (keyTimeBound := P.samplerTime)
    (keyWordsBound := P.samplerWords) (keyNames := P.samplerNames) (keyFits := P.samplerFits)
    (keyReserve := by have := P.scalar_reserve; omega) (challengeValid := P.challenge_valid) (post := post) (postFn := postFn) (postLaw := postLaw)

variable (correction : F → Period × F → F) (final : F → SynchronizedPS.Forgery F Period → F) (keysOf : F → G₂ → G₂ → G₂ × G₂)
  (postEq : ∀ kappa g X g₂ s, postFn ((kappa, (g, X)), (((kappa • g₂, s • g₂), s), ((kappa • g₂, s • g₂), s))) =
    ((kappa, (g, X)), ((keysOf s g₂ (kappa • g₂), s), (keysOf s g₂ (kappa • g₂), s))))
  (corrLaw : ∀ (d : P.core.scalar.Value) (m : P.core.message.Value), (side.routines.corrFn (d, m)).val = correction d.val m.val)
  (finLaw : ∀ (d : P.core.scalar.Value) (m : Period × F), side.finish.negFn (side.finish.finFn (d.val, m)) = -(final d.val m))
  (keysValid : ∀ (s : P.scalar.Value) (α : F), P.core.inner.key.valid (keysOf s.val keyGenerator (α • keyGenerator)))

include postEq corrLaw finLaw keysValid in
/-- At the curve's generators, the wrapped-attacker bad solver has the executed bad solver's
distribution: the public-key sample and the known key are drawn in the other order. -/
theorem bad_eq (X : G₁) (α : F) :
    𝒟[($ᵗ F : ProbComp F) >>= fun y =>
      badReductionList terms (wrap (correction y) (final y) (keysOf y keyGenerator) (SynchronizedPS.Proofs.view A.source generator)) generator X keyGenerator (α • keyGenerator)] =
    𝒟[A.caliperBad (terms := terms) side postFn generator X keyGenerator (α • keyGenerator)] := by
  unfold caliperBad badReductionList
  refine evalDist_eq_of_evalSPMF_eq _ _ ?_
  rw [OracleComp.DeferredSampling.evalSPMF_bind_comm]
  congr 1
  rw [← P.scalarLaw]
  simp only [bind_map_left]
  refine bind_congr fun kappa => bind_congr fun s => ?_
  show (simulateQ BLS.LazyAGM.Reduction.privateListOracle (badProgram terms generator X (kappa.val • keyGenerator) kappa.val _)).run' [] =
    (simulateQ BLS.LazyAGM.Reduction.privateListOracle (badProgram terms (postFn _).1.2.1 (postFn _).1.2.2 (postFn _).2.2 (postFn _).1.1 _)).run' []
  rw [postEq]
  unfold AlgebraicAdversary.outerAdversary
  rw [badProgram_congr terms generator X kappa.val (Wrapper.outerAdversary_main_eq side.routines A.caller P.wrapper P.outLe side.finish P.messageTotal
    queries.total A.invariant A.correspondence (SynchronizedPS.Proofs.view A.source generator) A.source_eq correction final (keysOf s.val keyGenerator) corrLaw finLaw side.mulLaw
    P.fuelRoom ⟨keysOf s.val keyGenerator (kappa.val • keyGenerator), keysValid s kappa.val⟩ s (kappa.val • keyGenerator) rfl).symm]

include postEq corrLaw finLaw keysValid in
theorem bad_advantage_eq :
    Model.dlog11Advantage generator keyGenerator (fun g X g₂ Z₂ => ($ᵗ F : ProbComp F) >>= fun y =>
      badReductionList terms (wrap (correction y) (final y) (keysOf y g₂) (SynchronizedPS.Proofs.view A.source generator)) g X g₂ Z₂) =
    Model.dlog11Advantage generator keyGenerator (A.caliperBad (terms := terms) side postFn) :=
  BLS.LazyAGM.Reduction.dlog11Advantage_congr generator keyGenerator _ (A.caliperBad (terms := terms) side postFn)
    (fun α => A.bad_eq side postFn correction final keysOf postEq corrLaw finLaw keysValid (α • generator) α)

include postLaw reserve in
theorem caliperBad_within' (codeLe : P.badWords side bs post.words ≤ P.solverCode)
    (memoryLe : P.badMemory side bs post.time post.words post.slots ≤ P.solverMemory) :
    P.within (P.badTime side bs post.time) (A.caliperBad (terms := terms) side postFn) :=
  (A.caliperBad_within side reserve bs post postFn postLaw).mono codeLe memoryLe le_rfl

include postEq corrLaw finLaw keysValid postLaw reserve in
theorem bad_advantage (codeLe : P.badWords side bs post.words ≤ P.solverCode)
    (memoryLe : P.badMemory side bs post.time post.words post.slots ≤ P.solverMemory) :
    Model.dlog11Advantage generator keyGenerator (fun g X g₂ Z₂ => ($ᵗ F : ProbComp F) >>= fun y =>
      badReductionList terms (wrap (correction y) (final y) (keysOf y g₂) (SynchronizedPS.Proofs.view A.source generator)) g X g₂ Z₂) ≤
    P.dlogBound (P.badTime side bs post.time) :=
  (A.bad_advantage_eq side postFn correction final keysOf postEq corrLaw finLaw keysValid).trans_le
    (Model.le_advantageBound _ _ _ (A.caliperBad_within' side reserve bs post postFn postLaw codeLe memoryLe))
end Bad

/-! ## The four solvers -/

theorem keysValid₁ (s : P.scalar.Value) (α : F) : P.core.inner.key.valid (α • keyGenerator, s.val • keyGenerator) :=
  ⟨P.key_valid α, P.key_valid s.val⟩
theorem keysValid₂ (s : P.scalar.Value) (α : F) : P.core.inner.key.valid (s.val • keyGenerator, α • keyGenerator) :=
  ⟨P.key_valid s.val, P.key_valid α⟩
theorem finLaw₁ (d : P.core.scalar.Value) (m : Period × F) :
    P.wrap₁.finish.negFn (P.wrap₁.finish.finFn (d.val, m)) = -(final₁ d.val m) := by
  rw [P.wrap₁.finLaw, P.wrap₁.negLaw]
  simp [final₁]
theorem finLaw₂ (d : P.core.scalar.Value) (m : Period × F) :
    P.wrap₂.finish.negFn (P.wrap₂.finish.finFn (d.val, m)) = -(final₂ d.val m) := by
  rw [P.wrap₂.finLaw, P.wrap₂.negLaw]
  simp [final₂]

theorem good₁_advantage : Model.dlog11Advantage generator keyGenerator (solverGood₁ (SynchronizedPS.Proofs.view A.source generator)) ≤ P.dlogBound P.goodTime₁ :=
  A.good_advantage P.wrap₁ P.reserve₁ P.good₁ P.postGood₁ (fun value => value) (KeyedSetup.keepStage_source P.shape.keyed P.outer.port)
    correction₁ final₁ (fun y g₂ pk => (pk, y • g₂)) (fun _ _ _ _ _ => rfl) P.wrap₁.corrLaw finLaw₁ keysValid₁
    (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) (le_max_left _ _))
theorem bad₁_advantage : Model.dlog11Advantage generator keyGenerator (solverBad₁ (SynchronizedPS.Proofs.view A.source generator)) ≤ P.dlogBound P.badTime₁ :=
  A.bad_advantage P.wrap₁ P.reserve₁ P.bad₁ P.postBad₁ (fun value => value) (KeyedSetup.keepStage_source P.shape.badKeyed P.outer.port)
    correction₁ final₁ (fun y g₂ pk => (pk, y • g₂)) (fun _ _ _ _ _ => rfl) P.wrap₁.corrLaw finLaw₁ keysValid₁
    (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) (le_max_left _ _))
theorem good₂_advantage : Model.dlog11Advantage generator keyGenerator (solverGood₂ (SynchronizedPS.Proofs.view A.source generator)) ≤ P.dlogBound P.goodTime₂ :=
  A.good_advantage P.wrap₂ P.reserve₂ P.good₂ P.postGood₂ KeyedSetup.swapValue (KeyedSetup.swapStage_source P.shape.keyed P.outer.port)
    correction₂ final₂ (fun x g₂ pk => (x • g₂, pk)) (fun _ _ _ _ _ => rfl) P.wrap₂.corrLaw finLaw₂ keysValid₂
    (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) (le_max_right _ _))
theorem bad₂_advantage : Model.dlog11Advantage generator keyGenerator (solverBad₂ (SynchronizedPS.Proofs.view A.source generator)) ≤ P.dlogBound P.badTime₂ :=
  A.bad_advantage P.wrap₂ P.reserve₂ P.bad₂ P.postBad₂ KeyedSetup.swapValue (KeyedSetup.swapStage_source P.shape.badKeyed P.outer.port)
    correction₂ final₂ (fun x g₂ pk => (x • g₂, pk)) (fun _ _ _ _ _ => rfl) P.wrap₂.corrLaw finLaw₂ keysValid₂
    (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))

/-! ### The four executed solvers as a family -/

/-- The executed good solver of scheme₁. -/
noncomputable def caliperGood₁ : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := A.caliperGood (terms := terms₁) P.wrap₁ (fun value => value)
noncomputable def caliperBad₁ : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := A.caliperBad (terms := terms₁) P.wrap₁ (fun value => value)
noncomputable def caliperGood₂ : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := A.caliperGood (terms := terms₂) P.wrap₂ KeyedSetup.swapValue
noncomputable def caliperBad₂ : AlgebraicGroupModel.DLog11Adversary F G₁ G₂ := A.caliperBad (terms := terms₂) P.wrap₂ KeyedSetup.swapValue

theorem good₁_eq : Model.dlog11Advantage generator keyGenerator (solverGood₁ (SynchronizedPS.Proofs.view A.source generator)) =
    Model.dlog11Advantage generator keyGenerator A.caliperGood₁ :=
  A.good_advantage_eq (terms := terms₁) P.wrap₁ (fun value => value) correction₁ final₁ (fun y g₂ pk => (pk, y • g₂)) (fun _ _ _ _ _ => rfl)
    P.wrap₁.corrLaw finLaw₁ keysValid₁
theorem bad₁_eq : Model.dlog11Advantage generator keyGenerator (solverBad₁ (SynchronizedPS.Proofs.view A.source generator)) =
    Model.dlog11Advantage generator keyGenerator A.caliperBad₁ :=
  A.bad_advantage_eq (terms := terms₁) P.wrap₁ (fun value => value) correction₁ final₁ (fun y g₂ pk => (pk, y • g₂)) (fun _ _ _ _ _ => rfl)
    P.wrap₁.corrLaw finLaw₁ keysValid₁
theorem good₂_eq : Model.dlog11Advantage generator keyGenerator (solverGood₂ (SynchronizedPS.Proofs.view A.source generator)) =
    Model.dlog11Advantage generator keyGenerator A.caliperGood₂ :=
  A.good_advantage_eq (terms := terms₂) P.wrap₂ KeyedSetup.swapValue correction₂ final₂ (fun x g₂ pk => (x • g₂, pk)) (fun _ _ _ _ _ => rfl)
    P.wrap₂.corrLaw finLaw₂ keysValid₂
theorem bad₂_eq : Model.dlog11Advantage generator keyGenerator (solverBad₂ (SynchronizedPS.Proofs.view A.source generator)) =
    Model.dlog11Advantage generator keyGenerator A.caliperBad₂ :=
  A.bad_advantage_eq (terms := terms₂) P.wrap₂ KeyedSetup.swapValue correction₂ final₂ (fun x g₂ pk => (x • g₂, pk)) (fun _ _ _ _ _ => rfl)
    P.wrap₂.corrLaw finLaw₂ keysValid₂

theorem caliperGood₁_within : P.within P.goodTime₁ A.caliperGood₁ :=
  A.caliperGood_within' P.wrap₁ P.reserve₁ P.good₁ P.postGood₁ (fun value => value) (KeyedSetup.keepStage_source P.shape.keyed P.outer.port)
    (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) (le_max_left _ _))
theorem caliperBad₁_within : P.within P.badTime₁ A.caliperBad₁ :=
  A.caliperBad_within' P.wrap₁ P.reserve₁ P.bad₁ P.postBad₁ (fun value => value) (KeyedSetup.keepStage_source P.shape.badKeyed P.outer.port)
    (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) (le_max_left _ _))
theorem caliperGood₂_within : P.within P.goodTime₂ A.caliperGood₂ :=
  A.caliperGood_within' P.wrap₂ P.reserve₂ P.good₂ P.postGood₂ KeyedSetup.swapValue (KeyedSetup.swapStage_source P.shape.keyed P.outer.port)
    (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) (le_max_right _ _))
theorem caliperBad₂_within : P.within P.badTime₂ A.caliperBad₂ :=
  A.caliperBad_within' P.wrap₂ P.reserve₂ P.bad₂ P.postBad₂ KeyedSetup.swapValue (KeyedSetup.swapStage_source P.shape.badKeyed P.outer.port)
    (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) (le_max_right _ _))

end AlgebraicAdversary

end Signatures.Runtime.SyncWrapCaliper
