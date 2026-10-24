import Proofs.Runtime.Caliper.WeightedFullSource
import Proofs.Runtime.Caliper.WeightedFullBounds
import Proofs.Runtime.Caliper.DLog

/-! The complete weighted good reduction is an actual resource-bounded Caliper
solver. Its witness includes executed challenge setup and store initialization,
caller, lazy weighted service and extractor. Only local routine/caller contracts
and explicit representability bounds are supplied. -/
namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource OracleComp OracleSpec Model.LazyAGM
variable {w : Nat} {G M A PK J : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [DecidableEq J] [Field (val.Value base)] [SampleableType (val.Value base)]
    [AddCommGroup G] [Module (val.Value base) G]
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G (val.Value base) (val.Value base) (G × G) A)
    (setup : WeightedSetup.Layouts layout.service PK) (routines : Routines layout)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (caller : Caller layout setup.key.representation) (fuel : Nat)
    (source : ProbComp layout.service.evaluation.cache.value.Value)
    (coefficientLaw : routines.coefficientDefault.val = 0)
    (combineLaw : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (respondLaw : routines.respond = fun signing value => value.1 • (if signing then value.2.2 else value.2.1))
    (calculateLaw : routines.calculate = fun value => value.1 / (value.2.1 - value.2.2))
    (numeratorLaw : routines.numerator = fun value => value.1 + value.2)
    (invariant : Invariant layout setup caller fuel)
    (cacheRoom : max 1 layout.terms * (2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)
    (hashRoom : fuel ≤ layout.service.hashCapacityPred + 1)
    (signRoom : fuel ≤ layout.service.signCapacityPred + 1)
    (keys : J ≃ key.Value base) (terms : M → List (J × val.Value base))
    (termsEqual : ∀ message, routines.generate message = (terms message).map (Prod.map keys id))
    (witness : Correspondence layout setup caller fuel invariant keys)
    (adversary : Adversary (val.Value base) J M G PK)
    (same : ∀ pk : setup.key.Value,
      (fun answer => WeightedCallerProgram.output answer.val) <$> witness.source pk.val = adversary.main pk.val)

include coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw numeratorLaw cacheRoom hashRoom signRoom termsEqual same in
theorem good_source (value : setup.challenge.Value) :
    Subtype.val <$> denote layout setup routines P comparison correct caller fuel true source value =
      WeightedReduction.goodReductionList terms adversary value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2 := by
  have equality := denote_source layout setup caller fuel invariant keys routines P comparison correct true source
    coefficientLaw combineLaw zeroLaw uniform cacheRoom hashRoom signRoom terms termsEqual witness value
  rw [respondLaw, calculateLaw, numeratorLaw] at equality
  exact equality.trans (WeightedCallerProgram.good_original_finish terms Subtype.val (witness.source value.val.2.2)
    adversary value.val.1.1 value.val.1.2 value.val.2.1 value.val.2.2 (same ⟨value.val.2.2, value.property.2.2⟩))

variable [SMul (val.Value base) PK]
    (bound : Routines.Bounds layout routines) (localBound : Caller.Bounds layout setup caller)
    (draw : Interactive.Code w)
    (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    {drawTime drawWords drawSlots : Nat}
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.service.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawSlots)
    (drawFits : (draw.lower layout.port).DescriptionFits)
    (drawReserve : drawSlots + 5 < 2 ^ w)
    (handlerReserve : WeightedOracle.namesBudget routines.slots drawSlots routines.slots routines.slots +
      WeightedCallerHandler.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits
        layout.randomBound layout.randomFits bound.generator.words drawWords bound.update.words (fun signing => (bound.response signing).words) + 1 < 2 ^ w)
    (generator : G) (keyGenerator : PK)
    (challengeValid : ∀ scalar : val.Value base,
      setup.challenge.valid ((generator, scalar • generator), (keyGenerator, scalar • keyGenerator)))

include coefficientLaw combineLaw zeroLaw uniform respondLaw calculateLaw numeratorLaw cacheRoom hashRoom signRoom termsEqual same
    correct drawCorrect drawTimeBound drawWordsBound drawNames drawFits drawReserve handlerReserve challengeValid in
theorem good_dlogWithin : dlogWithin layout.port setup.challenge layout.extraction.scalar generator keyGenerator
    (codeBudget layout setup routines caller bound localBound true drawWords fuel)
    (memoryBudget layout setup routines caller bound localBound true drawTime drawWords drawSlots fuel)
    (timeBudget layout setup routines caller bound localBound true drawTime fuel)
    (WeightedReduction.goodReductionList terms adversary) := by
  refine ⟨challengeValid, ?_⟩
  exact (within layout setup routines caller bound localBound P comparison correct draw fuel true source drawCorrect drawTimeBound
    drawWordsBound drawNames invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform drawFits drawReserve handlerReserve).congr
      (good_source layout setup routines P comparison correct caller fuel source coefficientLaw combineLaw zeroLaw uniform
        respondLaw calculateLaw numeratorLaw invariant cacheRoom hashRoom signRoom keys terms termsEqual witness adversary same)
end Signatures.Runtime.CaliperBackend.WeightedFull
