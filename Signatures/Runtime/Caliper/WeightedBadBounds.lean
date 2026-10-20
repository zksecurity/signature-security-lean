import Signatures.Runtime.Caliper.WeightedBadProgram

/-! Resources of the complete sampled weighted bad program, including its
outer draw, key computation, initialization, caller and extraction. -/
namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {G F M A PK : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SMul F PK]
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G F (val.Value base) (F × (G × G)) A)
    (setup : WeightedSetup.Layouts layout.service PK) (resampling : Resampling layout setup)
    (routines : Routines layout) (caller : Caller layout setup.key.representation)
    (bound : Routines.Bounds layout routines) (localBound : Caller.Bounds layout setup caller)

def badTimeBudget (drawTime outerTime fuel : Nat) : Nat :=
  WeightedBadSetup.timeBudget resampling.preparation outerTime resampling.budget.time +
    timeBudget layout setup routines caller bound localBound false drawTime fuel

def badCodeBudget (drawWords outerWords fuel : Nat) : Nat :=
  WeightedBadSetup.codeBudget resampling.preparation outerWords resampling.budget.words +
    codeBudget layout setup routines caller bound localBound false drawWords fuel + 1

def badNameBudget (drawSlots outerSlots : Nat) : Nat :=
  max (max (max 3 outerSlots) resampling.slots) (nameBudget layout setup routines caller localBound drawSlots)

def badMemoryBudget (drawTime outerTime drawWords outerWords drawSlots outerSlots fuel : Nat) : Nat :=
  5 * badCodeBudget layout setup resampling routines caller bound localBound drawWords outerWords fuel +
    4 * badNameBudget layout setup resampling routines caller localBound drawSlots outerSlots + 3 +
    resampling.preparation.challenge.representation.encoding.words +
    badTimeBudget layout setup resampling routines caller bound localBound drawTime outerTime fuel

variable [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (draw outerDraw : Interactive.Code w) (fuel : Nat)
    (source : ProbComp layout.service.evaluation.cache.value.Value)
    (outerSource : ProbComp resampling.preparation.scalar.Value)
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
    (invariant : Invariant layout setup caller fuel)
    (cacheRoom : max 1 layout.terms * (2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)
    (hashRoom : fuel ≤ layout.service.hashCapacityPred + 1)
    (signRoom : fuel ≤ layout.service.signCapacityPred + 1)
    (combineLaw : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

include drawCorrect outerCorrect drawTimeBound outerTimeBound invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform in
theorem bad_time : Interactive.TimeBound layout.port .unit resampling.preparation.challenge.representation
    (badCode layout setup resampling routines P comparison correct caller draw outerDraw fuel)
    (badTimeBudget layout setup resampling routines caller bound localBound drawTime outerTime fuel) :=
  (WeightedBadSetup.time resampling.preparation resampling.scale resampling.names.buffers resampling.reserve resampling.bounded
    layout.port outerDraw outerSource outerCorrect outerTimeBound).seq
    (resample_refines layout setup resampling outerDraw outerSource outerCorrect)
    (time layout setup routines caller bound localBound P comparison correct draw fuel false source drawCorrect drawTimeBound
      invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform)

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include drawWordsBound outerWordsBound in
theorem bad_words : ((badCode layout setup resampling routines P comparison correct caller draw outerDraw fuel).lower layout.port).descriptionWords ≤
    badCodeBudget layout setup resampling routines caller bound localBound drawWords outerWords fuel := by
  have prepared := WeightedBadSetup.words resampling.preparation resampling.scale resampling.names.buffers resampling.reserve resampling.bounded
    layout.port outerDraw outerWordsBound
  have tailBound := words layout setup routines caller bound localBound P comparison correct draw fuel false drawWordsBound
  change ((resampleCode layout setup resampling outerDraw).lower layout.port).descriptionWords ≤ _ at prepared
  simp only [badCode, Interactive.Code.lower, WordIO.Code.descriptionWords_seq]
  unfold badCodeBudget
  omega

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include drawNames outerNames in
theorem bad_names : WordIO.NamesAccounted ((badCode layout setup resampling routines P comparison correct caller draw outerDraw fuel).lower layout.port)
    (badNameBudget layout setup resampling routines caller localBound drawSlots outerSlots) := by
  have prepared := WeightedBadSetup.names resampling.preparation resampling.scale resampling.names.buffers resampling.reserve
    resampling.names.accounted layout.port outerDraw outerNames
  have tailNames := names layout setup routines caller localBound P comparison correct draw fuel false drawNames
  exact (prepared.mono (Nat.le_max_left _ _)).seq (tailNames.mono (Nat.le_max_right _ _))

variable (drawFits : (draw.lower layout.port).DescriptionFits) (outerFits : (outerDraw.lower layout.port).DescriptionFits)
    (drawReserve : drawSlots + 5 < 2 ^ w) (outerReserve : outerSlots < 2 ^ w)
    (handlerReserve : WeightedOracle.namesBudget routines.slots drawSlots routines.slots routines.slots +
      WeightedCallerHandler.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits
        layout.randomBound layout.randomFits bound.generator.words drawWords bound.update.words (fun signing => (bound.response signing).words) + 1 < 2 ^ w)

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include drawWordsBound drawNames outerNames drawFits outerFits drawReserve outerReserve handlerReserve in
theorem bad_descriptionFits : ((badCode layout setup resampling routines P comparison correct caller draw outerDraw fuel).lower layout.port).DescriptionFits :=
  .seq layout.service.evaluation.cache.wordFits
    (WeightedBadSetup.descriptionFits resampling.preparation resampling.scale resampling.names.buffers resampling.reserve
      layout.port outerDraw outerFits outerNames outerReserve)
    (descriptionFits layout setup routines caller bound P comparison correct draw fuel false drawWordsBound drawNames drawFits drawReserve handlerReserve)

include drawCorrect outerCorrect drawTimeBound outerTimeBound drawWordsBound outerWordsBound drawNames outerNames
    invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform drawFits outerFits drawReserve outerReserve handlerReserve in
theorem bad_within : Interactive.Within layout.port resampling.preparation.challenge layout.extraction.scalar
    (badCodeBudget layout setup resampling routines caller bound localBound drawWords outerWords fuel)
    (badMemoryBudget layout setup resampling routines caller bound localBound drawTime outerTime drawWords outerWords drawSlots outerSlots fuel)
    (badTimeBudget layout setup resampling routines caller bound localBound drawTime outerTime fuel)
    (fun value => Subtype.val <$> badSource layout setup resampling routines P comparison correct caller fuel source outerSource value) :=
  Interactive.within_of_refines_accounted
    (bad_refines layout setup resampling routines P comparison correct caller draw outerDraw fuel source outerSource outerCorrect drawCorrect
      combineLaw zeroLaw uniform invariant cacheRoom hashRoom signRoom)
    (bad_time layout setup resampling routines caller bound localBound P comparison correct draw outerDraw fuel source outerSource
      drawCorrect outerCorrect drawTimeBound outerTimeBound invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform)
    (bad_words layout setup resampling routines caller bound localBound P comparison correct draw outerDraw fuel drawWordsBound outerWordsBound)
    (bad_names layout setup resampling routines caller localBound P comparison correct draw outerDraw fuel drawNames outerNames)
    (bad_descriptionFits layout setup resampling routines caller bound P comparison correct draw outerDraw fuel drawWordsBound drawNames outerNames
      drawFits outerFits drawReserve outerReserve handlerReserve)
end Signatures.Runtime.CaliperBackend.WeightedFull
