import Proofs.Runtime.Caliper.WeightedBadBounds
import Proofs.Runtime.Caliper.DLog

/-! The sampled, initialized, pair-cache program implements exactly the original
weighted bad reduction, and belongs to the fixed Caliper DLog resource class. -/
namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
variable {w : Nat} {G M A PK J : Type} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom}
    [DecidableEq (key.Value base)] [DecidableEq J] [Field (scalar.Value base)] [SampleableType (scalar.Value base)]
    [AddCommGroup G] [Module (scalar.Value base) G]
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G (scalar.Value base)
      ((Ty.pair scalar scalar).Value base) (scalar.Value base × (G × G)) A)
    (setup : WeightedSetup.Layouts layout.service PK) (routines : Routines (base := base) (key := key) (val := .pair scalar scalar) layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller (base := base) (key := key) (val := .pair scalar scalar) layout setup.key.representation) (fuel : Nat)
    (source : ProbComp layout.service.evaluation.cache.value.Value)
    (coefficientLaw : routines.coefficientDefault.val = 0)
    (combineLaw : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ ((Ty.pair scalar scalar).Value base) : ProbComp _))
    (respondLaw : routines.respond = fun signing value =>
      if signing then value.2.1 • (value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1)
      else value.1.1 • value.2.2.2 + value.1.2 • value.2.2.1)
    (calculateLaw : routines.calculate = fun value => -(value.2.1.2 - value.2.2.2) / (value.2.1.1 - value.2.2.1))
    (invariant : Invariant (base := base) (key := key) (val := .pair scalar scalar) layout setup caller fuel)
    (cacheRoom : max 1 layout.terms * (2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)
    (hashRoom : fuel ≤ layout.service.hashCapacityPred + 1)
    (signRoom : fuel ≤ layout.service.signCapacityPred + 1)
    (keys : J ≃ key.Value base) (terms : M → List (J × scalar.Value base))
    (termsEqual : ∀ message, routines.generate message = (terms message).map (Prod.map keys id))
    (witness : Correspondence (base := base) (key := key) (val := .pair scalar scalar) layout setup caller fuel invariant keys)
    (adversary : Adversary (scalar.Value base) J M G PK)
    (same : ∀ pk : setup.key.Value,
      (fun answer => WeightedCallerProgram.output answer.val) <$> witness.source pk.val = adversary.main pk.val)

include coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw cacheRoom hashRoom signRoom termsEqual same in
theorem bad_fixed_source (value : setup.challenge.Value) :
    Subtype.val <$> denote (base := base) (key := key) (val := .pair scalar scalar) layout setup routines P comparison correct caller fuel false source value =
      (simulateQ BLS.LazyAGM.Reduction.privateListOracle
        (WeightedReduction.badProgram terms value.val.1.2.1 value.val.1.2.2 value.val.2.2 value.val.1.1 adversary)).run' [] := by
  have equality := denote_source (base := base) (key := key) (val := .pair scalar scalar) layout setup caller fuel invariant keys routines P comparison correct false source
    coefficientLaw combineLaw zeroLaw uniform cacheRoom hashRoom signRoom terms termsEqual witness value
  rw [respondLaw, calculateLaw] at equality
  exact equality.trans (WeightedCallerProgram.bad_original_finish terms Subtype.val (witness.source value.val.2.2)
    adversary value.val.1.2.1 value.val.1.2.2 value.val.2.2 (same ⟨value.val.2.2, value.property.2.2⟩)
    value.val.1.1 routines.numerator)

variable [AddCommGroup PK] [Module (scalar.Value base) PK]
    (resampling : Resampling (base := base) (key := key) (val := .pair scalar scalar) layout setup) (outerSource : ProbComp resampling.preparation.scalar.Value)
    (outerUniform : Subtype.val <$> outerSource = ($ᵗ (scalar.Value base) : ProbComp _))

include coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw cacheRoom hashRoom signRoom termsEqual same outerUniform in
theorem bad_source (value : resampling.preparation.challenge.Value) :
    Subtype.val <$> badSource (base := base) (key := key) (val := .pair scalar scalar) layout setup resampling routines P comparison correct caller fuel source outerSource value =
      WeightedReduction.badReductionList terms adversary value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2 := by
  simp only [badSource, resampleSource, WeightedBadSetup.denote, WeightedReduction.badReductionList, map_bind, bind_map_left]
  rw [← outerUniform, bind_map_left]
  apply bind_congr
  intro sampled
  have fixed := bad_fixed_source layout setup routines P comparison correct caller fuel source coefficientLaw combineLaw zeroLaw uniform
    respondLaw calculateLaw invariant cacheRoom hashRoom signRoom keys terms termsEqual witness adversary same
    (Resampling.view (base := base) (key := key) (val := .pair scalar scalar) layout setup resampling (WeightedBadSetup.result resampling.preparation resampling.scale resampling.names.buffers
      resampling.reserve (WeightedBadSetup.sampledValue resampling.preparation value sampled)))
  simpa only [Resampling.view_val, WeightedBadSetup.result, WeightedBadSetup.sampledValue] using fixed

variable (bound : Routines.Bounds (base := base) (key := key) (val := .pair scalar scalar) layout routines) (localBound : Caller.Bounds (base := base) (key := key) (val := .pair scalar scalar) layout setup caller)
    (draw outerDraw : Interactive.Code w)
    (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    (outerCorrect : Interactive.Refines layout.port .unit resampling.preparation.unit.representation
      resampling.preparation.scalar.representation (fun _ => outerSource) outerDraw)
    {drawTime outerTime drawWords outerWords drawSlots outerSlots : Nat}
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.service.evaluation.cache.lookup.unit.representation draw drawTime)
    (outerTimeBound : Interactive.TimeBound layout.port .unit resampling.preparation.unit.representation outerDraw outerTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (outerWordsBound : (outerDraw.lower layout.port).descriptionWords ≤ outerWords)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawSlots)
    (outerNames : WordIO.NamesBound (outerDraw.lower layout.port) outerSlots)
    (drawFits : (draw.lower layout.port).DescriptionFits) (outerFits : (outerDraw.lower layout.port).DescriptionFits)
    (drawReserve : drawSlots + 5 < 2 ^ w) (outerReserve : outerSlots < 2 ^ w)
    (handlerReserve : WeightedOracle.namesBudget routines.slots drawSlots routines.slots routines.slots +
      WeightedCallerHandler.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits
        layout.randomBound layout.randomFits bound.generator.words drawWords bound.update.words (fun signing => (bound.response signing).words) + 1 < 2 ^ w)
    (generator : G) (keyGenerator : PK)
    (challengeValid : ∀ scalar : scalar.Value base,
      resampling.preparation.challenge.valid ((generator, scalar • generator), (keyGenerator, scalar • keyGenerator)))

include coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw cacheRoom hashRoom signRoom termsEqual same outerUniform
    correct drawCorrect outerCorrect drawTimeBound outerTimeBound drawWordsBound outerWordsBound drawNames outerNames
    drawFits outerFits drawReserve outerReserve handlerReserve challengeValid in
theorem bad_dlogWithin : dlogWithin layout.port resampling.preparation.challenge layout.extraction.scalar generator keyGenerator
    (badCodeBudget (base := base) (key := key) (val := .pair scalar scalar) layout setup resampling routines caller bound localBound drawWords outerWords fuel)
    (badMemoryBudget (base := base) (key := key) (val := .pair scalar scalar) layout setup resampling routines caller bound localBound drawTime outerTime drawWords outerWords drawSlots outerSlots fuel)
    (badTimeBudget (base := base) (key := key) (val := .pair scalar scalar) layout setup resampling routines caller bound localBound drawTime outerTime fuel)
    (WeightedReduction.badReductionList terms adversary) := by
  refine ⟨challengeValid, ?_⟩
  exact (bad_within (base := base) (key := key) (val := .pair scalar scalar) layout setup resampling routines caller bound localBound P comparison correct draw outerDraw fuel source outerSource
    drawCorrect outerCorrect drawTimeBound outerTimeBound drawWordsBound outerWordsBound drawNames outerNames invariant cacheRoom hashRoom signRoom
    combineLaw zeroLaw uniform drawFits outerFits drawReserve outerReserve handlerReserve).congr
      (bad_source layout setup routines P comparison correct caller fuel source coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw
        invariant cacheRoom hashRoom signRoom keys terms termsEqual witness adversary same resampling outerSource outerUniform)
end Signatures.Runtime.CaliperBackend.WeightedFull
