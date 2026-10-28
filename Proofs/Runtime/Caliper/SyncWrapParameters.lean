import Proofs.Runtime.Caliper.SyncWrapSource
import Proofs.Runtime.Caliper.SyncWrapKeyed
import Proofs.Runtime.Caliper.SyncWrapFinishBounds
import Proofs.Runtime.Caliper.WeightedParameters
import Proofs.SynchronizedPS.WrappedSecurity

/-! Fixed Caliper models for synchronized PS. The parameters fix the inner caller's layouts, the
wrapper's capacities, one scalar sampler, the key scaling, the weighted routines of the two
schemes over the outer layouts, the wrapper routines (correction, finish) of the two schemes, and
numeric caller allowances; the attacker supplies one local caller and source witness for the
inner interface. All four solvers and their budgets are constructed from these components. -/
namespace Signatures.Runtime.SyncWrapCaliper
open Caliper OracleComp OracleSpec CaliperBackend BoundedSource CaliperBackend.SyncWrap WeightedFull
open Signatures.Runtime.WeightedCaliper (base scalarTy indexTy pairTy QueryAllowance)

set_option linter.unusedSectionVars false

variable (F G₁ G₂ Period : Type) [Field F] [SampleableType F] [DecidableEq Period]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- The outer caller serves the attacker's queries, one extra hash per signing query, and the
final hash. -/
def outerFuel (queries : QueryAllowance) : Nat := queries.total + queries.sign + 1

/-! ## Layouts -/

/-- The inner caller's layouts with the key as a pair of key-group layouts, and the wrapper's
slot capacity and storage bound. -/
structure Shape (w : Nat) (State : Type) where
  scheme : SharedScheme w Period (Period × F) G₁ F
  keyG₂ : Layout w G₂
  keysFits : keyG₂.representation.encoding.words + keyG₂.representation.encoding.words < 2 ^ w
  state : Representation w State
  randomBound : Nat
  randomFits : randomBound + 1 ≤ 2 ^ w
  goodCallerFits : 8 * (1 + state.encoding.words +
    (WeightedCallerPackets.request scheme.goodService randomBound randomFits).encoding.words +
    (WeightedCallerPackets.reply scheme.goodService randomBound randomFits).encoding.words +
    scheme.goodBounds.extraction.forgery.representation.encoding.words + scheme.goodService.store.representation.encoding.words) < 2 ^ w
  badCallerFits : 8 * (1 + state.encoding.words +
    (WeightedCallerPackets.request scheme.badService randomBound randomFits).encoding.words +
    (WeightedCallerPackets.reply scheme.badService randomBound randomFits).encoding.words +
    scheme.badBounds.extraction.forgery.representation.encoding.words + scheme.badService.store.representation.encoding.words) < 2 ^ w
  goodSetupFits : 16 * (scheme.goodService.store.representation.encoding.words +
    scheme.rows.response.points.representation.encoding.words + 2 * (keyG₂.prod keyG₂ keysFits).representation.encoding.words) < 2 ^ w
  badSetupFits : 16 * (scheme.badService.store.representation.encoding.words +
    scheme.rows.response.config.representation.encoding.words + 2 * (keyG₂.prod keyG₂ keysFits).representation.encoding.words) < 2 ^ w
  samplingFits : 16 * (scheme.rows.accumulation.cache.value.representation.encoding.words +
    scheme.rows.response.points.representation.encoding.words + 2 * (keyG₂.prod keyG₂ keysFits).representation.encoding.words) < 2 ^ w
  /-- Room for the keyed challenge of the bad branch, whose configuration carries a scalar. -/
  badKeyedFits : 16 * (scheme.rows.accumulation.cache.value.representation.encoding.words +
    scheme.rows.response.config.representation.encoding.words + 2 * keyG₂.representation.encoding.words) < 2 ^ w
  slotCap : Nat
  outWords : Nat
  storageFits : 256 * (4 + outWords + scheme.goodService.evaluation.coefficient.representation.encoding.words +
    (1 + slotCap * (1 + scheme.goodService.evaluation.coefficient.representation.encoding.words)) +
    state.encoding.words + scheme.goodService.message.representation.encoding.words +
    scheme.goodService.point.representation.encoding.words +
    scheme.goodBounds.extraction.forgery.representation.encoding.words + (keyG₂.prod keyG₂ keysFits).representation.encoding.words +
    (WeightedCallerPackets.request scheme.goodService randomBound randomFits).encoding.words +
    (WeightedCallerPackets.reply scheme.goodService randomBound randomFits).encoding.words) < 2 ^ w

namespace Shape
variable {w : Nat} {State : Type} (shape : Shape F G₁ G₂ Period w State)

def inner : SharedLayouts w Period (Period × F) G₁ F (G₂ × G₂) State where
  scheme := shape.scheme
  key := shape.keyG₂.prod shape.keyG₂ shape.keysFits
  state := shape.state
  randomBound := shape.randomBound
  randomFits := shape.randomFits
  goodCallerFits := shape.goodCallerFits
  badCallerFits := shape.badCallerFits
  goodSetupFits := shape.goodSetupFits
  badSetupFits := shape.badSetupFits
  samplingFits := shape.samplingFits

/-- The wrapper's core, typed at the `Ty` encoding so the wrapper's routines apply directly. -/
def core : Core w (indexTy.Value (base F Period)) (indexTy.Value (base F Period) × scalarTy.Value (base F Period)) G₁
    (scalarTy.Value (base F Period)) (G₂ × G₂) State :=
  ⟨shape.inner, shape.slotCap, shape.outWords, shape.storageFits⟩

abbrev scalar : Layout w F := shape.scheme.rows.accumulation.cache.value
abbrev points : Layout w (G₁ × G₁) := shape.scheme.rows.response.points
abbrev config : Layout w (F × (G₁ × G₁)) := shape.scheme.rows.response.config

theorem keys_words : (shape.keyG₂.prod shape.keyG₂ shape.keysFits).representation.encoding.words =
    shape.keyG₂.representation.encoding.words + shape.keyG₂.representation.encoding.words := rfl

/-- The known-key draw for the good branch: `(pk, k • g₂)` with `k`. -/
def keyed : KeyedSetup.Layouts w F (G₁ × G₁) G₂ where
  scalar := shape.scheme.rows.accumulation.cache.value
  config := shape.scheme.rows.response.points
  key := shape.keyG₂
  wordFits := shape.scheme.rows.accumulation.cache.wordFits
  storageFits := by have := shape.samplingFits; rw [keys_words] at this; omega

/-- The public-key resampling of the bad branch. -/
def preparation : WeightedBadSetup.Layouts w F G₁ G₂ where
  scalar := shape.scheme.rows.accumulation.cache.value
  points := shape.scheme.rows.response.points
  key := shape.keyG₂
  wordFits := shape.scheme.rows.accumulation.cache.wordFits
  storageFits := by have := shape.samplingFits; rw [keys_words] at this; omega

/-- The known-key draw for the bad branch, over the resampled challenge. -/
def badKeyed : KeyedSetup.Layouts w F (F × (G₁ × G₁)) G₂ where
  scalar := shape.scheme.rows.accumulation.cache.value
  config := shape.scheme.rows.response.config
  key := shape.keyG₂
  wordFits := shape.scheme.rows.accumulation.cache.wordFits
  storageFits := shape.badKeyedFits

/-- The DLog challenge layout shared by all four solvers. -/
abbrev challenge : Layout w ((G₁ × G₁) × (G₂ × G₂)) := shape.keyed.challenge
theorem preparation_challenge : shape.preparation.challenge = shape.keyed.challenge := rfl
theorem prepared : shape.preparation.output = shape.badKeyed.challenge := rfl
end Shape

/-- The wrapper's capacities and storage bounds over a shape. -/
structure Frame (w : Nat) (State : Type) where
  shape : Shape F G₁ G₂ Period w State
  caps : Capacities shape.scheme
  goodCallerFits : 8 * (1 + shape.core.wrapper.representation.encoding.words +
    (WeightedCallerPackets.request (enlarge shape.core.inner.scheme caps).goodService shape.core.inner.randomBound shape.core.inner.randomFits).encoding.words +
    (WeightedCallerPackets.reply (enlarge shape.core.inner.scheme caps).goodService shape.core.inner.randomBound shape.core.inner.randomFits).encoding.words +
    caps.goodBounds.extraction.forgery.representation.encoding.words +
    (enlarge shape.core.inner.scheme caps).goodService.store.representation.encoding.words) < 2 ^ w
  badCallerFits : 8 * (1 + shape.core.wrapper.representation.encoding.words +
    (WeightedCallerPackets.request (enlarge shape.core.inner.scheme caps).badService shape.core.inner.randomBound shape.core.inner.randomFits).encoding.words +
    (WeightedCallerPackets.reply (enlarge shape.core.inner.scheme caps).badService shape.core.inner.randomBound shape.core.inner.randomFits).encoding.words +
    caps.badBounds.extraction.forgery.representation.encoding.words +
    (enlarge shape.core.inner.scheme caps).badService.store.representation.encoding.words) < 2 ^ w
  goodSetupFits : 16 * ((enlarge shape.core.inner.scheme caps).goodService.store.representation.encoding.words +
    shape.core.inner.scheme.rows.response.points.representation.encoding.words + 2 * shape.core.key.representation.encoding.words) < 2 ^ w
  badSetupFits : 16 * ((enlarge shape.core.inner.scheme caps).badService.store.representation.encoding.words +
    shape.core.inner.scheme.rows.response.config.representation.encoding.words + 2 * shape.core.key.representation.encoding.words) < 2 ^ w
  samplingFits : 16 * (shape.core.inner.scheme.rows.accumulation.cache.value.representation.encoding.words +
    shape.core.inner.scheme.rows.response.points.representation.encoding.words + 2 * shape.core.key.representation.encoding.words) < 2 ^ w
  gammaRoom : shape.core.slotCap ≤ caps.gammaPred

namespace Frame
variable {w : Nat} {State : Type} (frame : Frame F G₁ G₂ Period w State)
def wrapper : Wrapper frame.shape.core :=
  ⟨frame.caps, frame.goodCallerFits, frame.badCallerFits, frame.goodSetupFits, frame.badSetupFits, frame.samplingFits, frame.gammaRoom⟩
abbrev outer := frame.wrapper.outer
theorem compatible : frame.shape.keyed.output = frame.outer.goodSetup.challenge := rfl
theorem badCompatible : frame.shape.badKeyed.output = frame.outer.badSetup.challenge := rfl
end Frame

/-! ## Routine contracts -/

/-- The good weighted routines of one scheme with their algebraic laws, budgets and address room. -/
structure GoodSide {w : Nat} {M A : Type} (layout : WeightedCallerExtraction.Layouts w Period M G₁ F F (G₁ × G₁) A)
    (terms : M → List (Period × F)) (drawWords drawSlots : Nat) where
  routines : Routines (base := base F Period) (key := indexTy) (val := scalarTy) layout
  bounds : Routines.Bounds (base := base F Period) (key := indexTy) (val := scalarTy) layout routines
  terms_eq : routines.generate = terms
  coefficient : routines.coefficientDefault.val = 0
  combine : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1
  response : routines.respond = fun signing value => value.1 • (if signing then value.2.2 else value.2.1)
  extract : routines.calculate = fun value => value.1 / (value.2.1 - value.2.2)
  sum : routines.numerator = fun value => value.1 + value.2
  addresses : WeightedOracle.namesBudget routines.slots drawSlots routines.slots routines.slots +
    WeightedCallerHandler.codeBudget (base := base F Period) (key := indexTy) (val := scalarTy) layout.service layout.terms layout.termCountFits layout.termStorageFits
      layout.randomBound layout.randomFits bounds.generator.words drawWords bounds.update.words
        (fun signing => (bounds.response signing).words) + 1 < 2 ^ w

/-- The bad weighted routines of one scheme. -/
structure BadSide {w : Nat} {M A : Type} (layout : WeightedCallerExtraction.Layouts w Period M G₁ F (F × F) (F × (G₁ × G₁)) A)
    (terms : M → List (Period × F)) (drawWords drawSlots : Nat) where
  routines : Routines (base := base F Period) (key := indexTy) (val := pairTy) layout
  bounds : Routines.Bounds (base := base F Period) (key := indexTy) (val := pairTy) layout routines
  terms_eq : routines.generate = terms
  coefficient : routines.coefficientDefault.val = 0
  combine : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1
  response : routines.respond = fun signing value =>
    if signing then value.2.1 • (value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1)
    else value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1
  extract : routines.calculate = fun value => -(value.2.1.2 - value.2.2.2) / (value.2.1.1 - value.2.2.1)
  addresses : WeightedOracle.namesBudget routines.slots drawSlots routines.slots routines.slots +
    WeightedCallerHandler.codeBudget (base := base F Period) (key := indexTy) (val := pairTy) layout.service layout.terms layout.termCountFits layout.termStorageFits
      layout.randomBound layout.randomFits bounds.generator.words drawWords bounds.update.words
        (fun signing => (bounds.response signing).words) + 1 < 2 ^ w

/-- The wrapper's local routines of one scheme: the correction scalar `corrSpec k m` and the
final scalar `finSpec k m*`, with hashing of the period and the fused multiply-add. -/
structure WrapSide {w : Nat} {A : Type}
    (core : Core w (indexTy.Value (base F Period)) (indexTy.Value (base F Period) × scalarTy.Value (base F Period)) G₁ (scalarTy.Value (base F Period)) (G₂ × G₂) A)
    (corrSpec finSpec : F → Period × F → F) where
  routines : SyncWrap.Routines core
  finish : SyncWrap.Wrapper.FinishRoutines core
  hashOfLaw : ∀ m, (routines.hashOfFn m).val = m.val.1
  fmaLaw : ∀ c h σ, (routines.fmaFn (c, (h, σ))).val = σ.val + c.val • h.val
  corrLaw : ∀ d m, (routines.corrFn (d, m)).val = corrSpec d.val m.val
  negLaw : ∀ c, finish.negFn c = -c
  mulLaw : ∀ a b, finish.mulFn (a, b) = a * b
  finLaw : ∀ d m, finish.finFn (d, m) = finSpec d m

/-! ## The parameters -/

variable (queries : QueryAllowance) (generator : G₁) (keyGenerator : G₂)

structure Parameters where
  wordBits : Nat
  State : Type
  frame : Frame F G₁ G₂ Period wordBits State
  outLe : frame.wrapper.outer.good.forgery.representation.encoding.words ≤ frame.shape.core.outWords
  callerLimits : WeightedFull.Caller.Limits
  callerReserve : callerLimits.slots + callerLimits.step.words + 50 < 2 ^ wordBits
  initialReserve : callerLimits.slots + callerLimits.initial.words + 50 < 2 ^ wordBits
  sampler : Interactive.Code wordBits
  scalarSource : ProbComp frame.shape.scalar.Value
  samplerCorrect : Interactive.Refines frame.outer.port .unit frame.outer.good.service.evaluation.cache.lookup.unit.representation
    frame.shape.scalar.representation (fun _ => scalarSource) sampler
  scalarLaw : Subtype.val <$> scalarSource = ($ᵗ F : ProbComp F)
  samplerBudget : WeightedFull.Budget
  samplerTime : Interactive.TimeBound frame.outer.port .unit frame.outer.good.service.evaluation.cache.lookup.unit.representation sampler samplerBudget.time
  samplerWords : (sampler.lower frame.outer.port).descriptionWords ≤ samplerBudget.words
  samplerSlots : Nat
  samplerNames : WordIO.NamesBound (sampler.lower frame.outer.port) samplerSlots
  samplerFits : (sampler.lower frame.outer.port).DescriptionFits
  samplerReserve : PairSampling.slots samplerSlots samplerSlots + 5 < 2 ^ wordBits
  keyScale : Implementation .unit frame.shape.keyed.arguments frame.shape.keyG₂ (fun value => value.1 • value.2)
  keySlots : Nat
  keyReserve : keySlots + 5 < 2 ^ wordBits
  keyBuffers : keyScale.program.code.memBound ≤ keySlots
  keyNames : NamesAccounted keyScale.program.code keySlots
  keyBudget : WeightedFull.Budget
  keyBound : keyScale.BoundedBy keyBudget.time keyBudget.words
  good₁ : GoodSide F G₁ Period frame.outer.good SynchronizedPS.Wrapped.terms₁ samplerBudget.words samplerSlots
  bad₁ : BadSide F G₁ Period frame.outer.bad SynchronizedPS.Wrapped.terms₁
    (PairSampling.codeBudget frame.shape.scalar frame.shape.scalar samplerBudget.words samplerBudget.words) (PairSampling.slots samplerSlots samplerSlots)
  good₂ : GoodSide F G₁ Period frame.outer.good SynchronizedPS.Wrapped.terms₂ samplerBudget.words samplerSlots
  bad₂ : BadSide F G₁ Period frame.outer.bad SynchronizedPS.Wrapped.terms₂
    (PairSampling.codeBudget frame.shape.scalar frame.shape.scalar samplerBudget.words samplerBudget.words) (PairSampling.slots samplerSlots samplerSlots)
  wrap₁ : WrapSide F G₁ G₂ Period frame.shape.core (fun y m => y * m.2) (fun y m => y * m.2)
  wrap₂ : WrapSide F G₁ G₂ Period frame.shape.core (fun x _ => x) (fun x _ => x)
  messageTotal : ∀ m, frame.shape.core.message.valid m
  cacheRoom : max 1 frame.outer.good.terms * (2 * outerFuel queries + 1) ≤ frame.outer.good.service.evaluation.cache.capacityPred + 1
  hashRoom : outerFuel queries ≤ frame.outer.good.service.hashCapacityPred + 1
  signRoom : outerFuel queries ≤ frame.outer.good.service.signCapacityPred + 1
  slotRoom : outerFuel queries + 1 ≤ frame.shape.core.slotCap
  wrapReserve₁ : wrap₁.routines.slots + callerLimits.slots + (wrap₁.finish.slots + 3) + 3 +
    3000000 * (frame.shape.core.bound + wrap₁.routines.words + frame.shape.core.snocWords + callerLimits.step.words + callerLimits.initial.words +
      frame.wrapper.finishWords outLe wrap₁.finish + 1) + 2 < 2 ^ wordBits
  wrapReserve₂ : wrap₂.routines.slots + callerLimits.slots + (wrap₂.finish.slots + 3) + 3 +
    3000000 * (frame.shape.core.bound + wrap₂.routines.words + frame.shape.core.snocWords + callerLimits.step.words + callerLimits.initial.words +
      frame.wrapper.finishWords outLe wrap₂.finish + 1) + 2 < 2 ^ wordBits
  generatorValid : frame.shape.scheme.rows.point.valid generator
  keyGeneratorValid : frame.shape.keyG₂.valid keyGenerator

end Signatures.Runtime.SyncWrapCaliper
