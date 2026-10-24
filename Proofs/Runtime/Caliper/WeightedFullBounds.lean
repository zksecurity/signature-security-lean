import Proofs.Runtime.Caliper.WeightedFullProgram
import Proofs.Runtime.Caliper.Within

/-! Complete initialized-program budgets derived from the individual routines,
caller steps and sampler. Every stored operand and every visited memory state is
covered by the same generated program's Caliper certificate. -/
namespace Signatures.Runtime.CaliperBackend.WeightedFull
open Caliper BoundedSource OracleComp OracleSpec

structure Budget where
  time : Nat
  words : Nat

variable {w : Nat} {C G F M A PK : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    (layout : WeightedCallerExtraction.Layouts w (key.Value base) M G F (val.Value base) C A)
    (setup : WeightedSetup.Layouts layout.service PK) (routines : Routines layout)
    (caller : Caller layout setup.key.representation)

structure Routines.Bounds where
  generator : Budget
  update : Budget
  response : Bool → Budget
  extract : Budget
  sum : Budget
  generatorBound : routines.generator.BoundedBy generator.time generator.words
  updateBound : routines.update.BoundedBy update.time update.words
  responseBound : ∀ signing, (routines.response signing).BoundedBy (response signing).time (response signing).words
  extractBound : routines.extract.BoundedBy extract.time extract.words
  sumBound : routines.sum.BoundedBy sum.time sum.words

structure Caller.Bounds where
  step : Budget
  initial : Budget
  localTime : ∀ value, caller.continuation.time value ≤ step.time
  initialTime : ∀ value, caller.initialCode.time value ≤ initial.time
  localWords : descriptionWords caller.continuation.code ≤ step.words
  initialWords : descriptionWords caller.initialCode.code ≤ initial.words
  slots : Nat
  localNames : NamesAccounted caller.continuation.code slots
  initialNames : NamesAccounted caller.initialCode.code slots

variable [DecidableEq (key.Value base)] (bound : Routines.Bounds layout routines) (localBound : Caller.Bounds layout setup caller)

def timeBudget (hashes : Bool) (drawTime fuel : Nat) : Nat :=
  200 * setup.width + WeightedCallerProgram.timeBudget layout hashes setup.key.representation.encoding.words
    bound.generator.time drawTime bound.update.time (fun signing => (bound.response signing).time)
    localBound.step.time localBound.initial.time fuel bound.extract.time bound.sum.time

def codeBudget (hashes : Bool) (drawWords fuel : Nat) : Nat :=
  700 * setup.width + 252 + WeightedCallerProgram.codeBudget layout hashes setup.key.representation.encoding.words
    bound.generator.words drawWords bound.update.words (fun signing => (bound.response signing).words)
    localBound.step.words localBound.initial.words fuel bound.extract.words bound.sum.words

def nameBudget (drawNames : Nat) : Nat :=
  max 5 (max localBound.slots (max routines.slots (max drawNames
    (WeightedExtractor.nameBudget routines.slots drawNames routines.slots routines.slots routines.slots))))

def memoryBudget (hashes : Bool) (drawTime drawWords drawNames fuel : Nat) : Nat :=
  5 * codeBudget layout setup routines caller bound localBound hashes drawWords fuel +
    4 * nameBudget layout setup routines caller localBound drawNames + 3 + setup.challenge.representation.encoding.words +
    timeBudget layout setup routines caller bound localBound hashes drawTime fuel

variable [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
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

include drawCorrect drawTimeBound invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform in
theorem time : Interactive.TimeBound layout.port .unit setup.challenge.representation
    (code layout setup routines P comparison correct caller draw fuel hashes)
    (timeBudget layout setup routines caller bound localBound hashes drawTime fuel) := by
  have prepared := Interactive.TimeBound.compute (port := layout.port) (cost := .unit) (WeightedSetup.realizer setup)
    (200 * setup.width) (WeightedSetup.bounded setup).time_le
  have tailBound := WeightedCallerProgram.time layout routines.generator P comparison correct
    routines.update routines.updateNames.buffers (by have := routines.reserve; omega) draw
    routines.response (fun signing => (routines.responseNames signing).buffers) (by have := routines.reserve; omega)
    caller.advance caller.continuation caller.localNameFits setup.key.representation
    caller.initial caller.initialCode caller.initialNameFits setup.outputFits fuel
    routines.coefficientDefault hashes routines.extract routines.extractNames.buffers (by have := routines.reserve; omega)
    routines.sum routines.sumNames.buffers (by have := routines.reserve; omega) source drawCorrect
    bound.generatorBound drawTimeBound bound.updateBound bound.extractBound bound.sumBound
    combineLaw zeroLaw uniform invariant.domain invariant.advanceValid (empty layout setup)
    (initial_valid layout setup caller fuel invariant) (initial_reserved layout setup fuel cacheRoom hashRoom signRoom)
    (initial_room layout setup fuel cacheRoom) bound.responseBound localBound.localTime localBound.initialTime
  have joined := Interactive.TimeBoundOn.seq
    ((Interactive.Refines.compute layout.port .unit (WeightedSetup.realizer setup)).on (fun _ => True))
    (prepared.on (fun _ => True)) tailBound (by
      intro value _ answer supported
      have same : answer = setup.start value := by simpa only [support_pure, Set.mem_singleton_iff] using supported
      subst answer
      rfl)
  intro tape value before holds finished reached
  exact joined tape value trivial before holds finished reached

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include drawWordsBound in
theorem words : ((code layout setup routines P comparison correct caller draw fuel hashes).lower layout.port).descriptionWords ≤
    codeBudget layout setup routines caller bound localBound hashes drawWords fuel := by
  have prepared := (WeightedSetup.bounded setup).code_le
  have tailBound := WeightedCallerProgram.words layout routines.generator P comparison correct
    routines.update routines.updateNames.buffers (by have := routines.reserve; omega) draw
    routines.response (fun signing => (routines.responseNames signing).buffers) (by have := routines.reserve; omega)
    caller.advance caller.continuation caller.localNameFits setup.key.representation
    caller.initial caller.initialCode caller.initialNameFits setup.outputFits fuel
    routines.coefficientDefault hashes routines.extract routines.extractNames.buffers (by have := routines.reserve; omega)
    routines.sum routines.sumNames.buffers (by have := routines.reserve; omega)
    bound.generatorBound drawWordsBound bound.updateBound bound.extractBound bound.sumBound
    bound.responseBound localBound.localWords localBound.initialWords
  change ((tail layout setup routines P comparison correct caller draw fuel hashes).lower layout.port).descriptionWords ≤ _ at tailBound
  change descriptionWords (WeightedSetup.realizer setup).code ≤ _ at prepared
  simp only [code, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  unfold codeBudget
  omega

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include drawNames in
theorem names : WordIO.NamesAccounted ((code layout setup routines P comparison correct caller draw fuel hashes).lower layout.port)
    (nameBudget layout setup routines caller localBound drawSlots) := by
  have tailNames := WeightedCallerProgram.names layout routines.generator P comparison correct
    routines.update routines.updateNames.buffers (by have := routines.reserve; omega) draw
    routines.response (fun signing => (routines.responseNames signing).buffers) (by have := routines.reserve; omega)
    caller.advance caller.continuation caller.localNameFits setup.key.representation
    caller.initial caller.initialCode caller.initialNameFits setup.outputFits fuel
    routines.coefficientDefault hashes routines.extract routines.extractNames.buffers (by have := routines.reserve; omega)
    routines.sum routines.sumNames.buffers (by have := routines.reserve; omega)
    (callerSlots := nameBudget layout setup routines caller localBound drawSlots)
    (by unfold nameBudget; omega) routines.generatorNames.accounted drawNames routines.updateNames.accounted
    (fun signing => (routines.responseNames signing).accounted) routines.extractNames.accounted routines.sumNames.accounted
    (by unfold nameBudget; omega) (by unfold nameBudget; omega) (by unfold nameBudget; omega) (by unfold nameBudget; omega)
    (localBound.localNames.mono (by unfold nameBudget; omega))
    (localBound.initialNames.mono (by unfold nameBudget; omega)) (by unfold nameBudget; omega)
  exact ((WordIO.NamesAccounted.compute (WeightedSetup.names setup)).mono (by unfold nameBudget; omega)).seq tailNames

variable (drawFits : (draw.lower layout.port).DescriptionFits)
    (drawReserve : drawSlots + 5 < 2 ^ w)
    (handlerReserve : WeightedOracle.namesBudget routines.slots drawSlots routines.slots routines.slots +
      WeightedCallerHandler.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits
        layout.randomBound layout.randomFits bound.generator.words drawWords bound.update.words (fun signing => (bound.response signing).words) + 1 < 2 ^ w)

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include drawWordsBound drawNames drawFits drawReserve handlerReserve in
theorem descriptionFits : ((code layout setup routines P comparison correct caller draw fuel hashes).lower layout.port).DescriptionFits := by
  have tailFits := WeightedCallerProgram.descriptionFits layout routines.generator P comparison correct
    routines.update routines.updateNames.buffers (by have := routines.reserve; omega) draw
    routines.response (fun signing => (routines.responseNames signing).buffers) (by have := routines.reserve; omega)
    caller.advance caller.continuation caller.localNameFits setup.key.representation
    caller.initial caller.initialCode caller.initialNameFits setup.outputFits fuel
    routines.coefficientDefault hashes routines.extract routines.extractNames.buffers (by have := routines.reserve; omega)
    routines.sum routines.sumNames.buffers (by have := routines.reserve; omega)
    bound.generatorBound drawWordsBound bound.updateBound bound.responseBound routines.generatorNames.buffers
    (by have := routines.reserve; omega) routines.generatorNames.accounted drawFits drawNames drawReserve
    (by have := routines.reserve; omega) routines.updateNames.accounted
    (fun signing => (routines.responseNames signing).accounted) handlerReserve
  exact .seq layout.service.evaluation.cache.wordFits (.compute (WeightedSetup.realizer setup).description_fits) tailFits

include drawCorrect drawTimeBound drawWordsBound drawNames invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform
    drawFits drawReserve handlerReserve in
theorem within : Interactive.Within layout.port setup.challenge layout.extraction.scalar
    (codeBudget layout setup routines caller bound localBound hashes drawWords fuel)
    (memoryBudget layout setup routines caller bound localBound hashes drawTime drawWords drawSlots fuel)
    (timeBudget layout setup routines caller bound localBound hashes drawTime fuel)
    (fun value => Subtype.val <$> denote layout setup routines P comparison correct caller fuel hashes source value) :=
  Interactive.within_of_refines_accounted
    (refines layout setup routines P comparison correct caller draw fuel hashes source invariant cacheRoom hashRoom signRoom
      drawCorrect combineLaw zeroLaw uniform)
    (time layout setup routines caller bound localBound P comparison correct draw fuel hashes source drawCorrect drawTimeBound
      invariant cacheRoom hashRoom signRoom combineLaw zeroLaw uniform)
    (words layout setup routines caller bound localBound P comparison correct draw fuel hashes drawWordsBound)
    (names layout setup routines caller localBound P comparison correct draw fuel hashes drawNames)
    (descriptionFits layout setup routines caller bound P comparison correct draw fuel hashes drawWordsBound drawNames
      drawFits drawReserve handlerReserve)
end Signatures.Runtime.CaliperBackend.WeightedFull
