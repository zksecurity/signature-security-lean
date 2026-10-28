import Proofs.Runtime.Caliper.WeightedFullBounds
import Proofs.Runtime.Caliper.WeightedFullSource

/-! Preparation stages in front of the complete initialized weighted program. A stage is
executed code that turns one represented challenge into another together with its
refinement and resource certificates; stages compose sequentially, and any stage whose
output is the program's challenge yields a bounded solver for the composed source. -/
namespace Signatures.Runtime.CaliperBackend.Preparation
open Caliper BoundedSource OracleComp OracleSpec

structure Stage {w : Nat} {X Y : Type} (port : Interactive.Port w unifSpec) (input : Layout w X) (output : Layout w Y) where
  code : Interactive.Code w
  source : input.Value → ProbComp output.Value
  refines : Interactive.Refines port .unit input.representation output.representation source code
  time : Nat
  words : Nat
  slots : Nat
  timeBound : Interactive.TimeBound port .unit input.representation code time
  wordsBound : (code.lower port).descriptionWords ≤ words
  names : WordIO.NamesAccounted (code.lower port) slots
  fits : (code.lower port).DescriptionFits

variable {w : Nat} {X Y Z : Type} {port : Interactive.Port w unifSpec}
    {input : Layout w X} {middle : Layout w Y} {output : Layout w Z}

def Stage.seq (hw : 16 < 2 ^ w) (first : Stage port input middle) (second : Stage port middle output) :
    Stage port input output where
  code := .seq first.code second.code
  source value := first.source value >>= second.source
  refines := first.refines.seq second.refines
  time := first.time + second.time
  words := first.words + second.words + 1
  slots := max first.slots second.slots
  timeBound := first.timeBound.seq first.refines second.timeBound
  wordsBound := by
    have := first.wordsBound
    have := second.wordsBound
    simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_seq]
    omega
  names := (first.names.mono (le_max_left _ _)).seq (second.names.mono (le_max_right _ _))
  fits := .seq hw first.fits second.fits

end Signatures.Runtime.CaliperBackend.Preparation

namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource OracleComp OracleSpec Preparation

variable {w : Nat} {C G F M A PK X : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G F (val.Value base) C A)
    (setup : WeightedSetup.Layouts layout.service PK)
    (routines : Routines layout) (caller : Caller layout setup.key.representation)
    (bound : Routines.Bounds layout routines) (localBound : Caller.Bounds layout setup caller)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    (draw : Interactive.Code w) (fuel : Nat) (hashes : Bool)
    (source : ProbComp layout.service.evaluation.cache.value.Value)
    (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    {drawTime drawWords drawSlots : Nat}
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.service.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawSlots)
    (invariant : Invariant layout setup caller fuel)
    (cacheRoom : max 1 layout.terms * (2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)
    (hashRoom : fuel ≤ layout.service.hashCapacityPred + 1)
    (signRoom : fuel ≤ layout.service.signCapacityPred + 1)
    (combineLaw : ∀ value, routines.combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (drawFits : (draw.lower layout.port).DescriptionFits)
    (drawReserve : drawSlots + 5 < 2 ^ w)
    (handlerReserve : WeightedOracle.namesBudget routines.slots drawSlots routines.slots routines.slots +
      WeightedCallerHandler.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits
        layout.randomBound layout.randomFits bound.generator.words drawWords bound.update.words (fun signing => (bound.response signing).words) + 1 < 2 ^ w)
    {input : Layout w X} (stage : Stage layout.port input setup.challenge)

include drawCorrect drawTimeBound drawWordsBound drawNames invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform
    drawFits drawReserve handlerReserve in
/-- The complete initialized program as a stage of its own. -/
def fullStage : Stage layout.port setup.challenge layout.extraction.scalar where
  code := code layout setup routines P comparison correct caller draw fuel hashes
  source := denote layout setup routines P comparison correct caller fuel hashes source
  refines := refines layout setup routines P comparison correct caller draw fuel hashes source invariant cacheRoom hashRoom signRoom
    drawCorrect combineLaw zeroLaw uniform
  time := timeBudget layout setup routines caller bound localBound hashes drawTime fuel
  words := codeBudget layout setup routines caller bound localBound hashes drawWords fuel
  slots := nameBudget layout setup routines caller localBound drawSlots
  timeBound := time layout setup routines caller bound localBound P comparison correct draw fuel hashes source drawCorrect drawTimeBound
    invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform
  wordsBound := words layout setup routines caller bound localBound P comparison correct draw fuel hashes drawWordsBound
  names := names layout setup routines caller localBound P comparison correct draw fuel hashes drawNames
  fits := descriptionFits layout setup routines caller bound P comparison correct draw fuel hashes drawWordsBound drawNames drawFits
    drawReserve handlerReserve

include drawCorrect drawTimeBound drawWordsBound drawNames invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform
    drawFits drawReserve handlerReserve in
/-- A prepared challenge followed by the complete program is a bounded solver for the
composed source. -/
theorem stage_within :
    Interactive.Within layout.port input layout.extraction.scalar
      (stage.words + codeBudget layout setup routines caller bound localBound hashes drawWords fuel + 1)
      (5 * (stage.words + codeBudget layout setup routines caller bound localBound hashes drawWords fuel + 1) +
        4 * max stage.slots (nameBudget layout setup routines caller localBound drawSlots) + 3 +
        input.representation.encoding.words +
        (stage.time + timeBudget layout setup routines caller bound localBound hashes drawTime fuel))
      (stage.time + timeBudget layout setup routines caller bound localBound hashes drawTime fuel)
      (fun value => Subtype.val <$> (stage.source value >>=
        denote layout setup routines P comparison correct caller fuel hashes source)) :=
  let composed := stage.seq layout.service.evaluation.cache.wordFits
    (fullStage layout setup routines caller bound localBound P comparison correct draw fuel hashes source drawCorrect
      drawTimeBound drawWordsBound drawNames invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform drawFits drawReserve handlerReserve)
  Interactive.within_of_refines_accounted composed.refines composed.timeBound composed.wordsBound composed.names composed.fits

end Signatures.Runtime.CaliperBackend.WeightedFull
