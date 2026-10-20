import Signatures.Runtime.Caliper.WeightedCallerExtraction

/-! Complete caller and terminal resource formulas add the constructed
weighted handler, local caller routines, exit routing and extraction. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerExtraction
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {C G F M A U : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (layout : Layouts w (key.Value base) M G F (val.Value base) C A)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit layout.service.message
      (GeneratedWeighted.terms layout.service.evaluation layout.terms layout.termCountFits layout.termStorageFits) generate)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit layout.service.evaluation.combine layout.service.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.service.responseInput layout.service.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)
    (advance : A × layout.Reply → layout.forgery.Value ⊕ (layout.Request × A))
    (continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → layout.forgery.Value ⊕ (layout.Request × A))
    (initialCode : Realizer .unit input (CallerStep.next layout.control) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.service.store.representation.encoding.words < 2 ^ w)
    (fuel : Nat)

def timeBudget (inputWords generatorTime drawTime updateTime : Nat) (responseTime : Bool → Nat)
    (localTime initialTime fuel extractTime : Nat) : Nat :=
  WeightedCaller.timeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits layout.randomBound layout.randomFits
    inputWords (CallerStep.width layout.control) generatorTime drawTime updateTime responseTime localTime initialTime fuel +
    WeightedCallerFinish.timeBudget layout.extraction layout.config.representation layout.pending layout.exitFits extractTime
def codeBudget (inputWords generatorWords drawWords updateWords : Nat) (responseWords : Bool → Nat)
    (localWords initialWords fuel extractWords : Nat) : Nat :=
  WeightedCaller.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits layout.randomBound layout.randomFits
    inputWords (CallerStep.width layout.control) generatorWords drawWords updateWords responseWords localWords initialWords fuel +
    WeightedCallerFinish.codeBudget layout.extraction layout.config.representation layout.pending layout.exitFits extractWords + 1

variable (source : ProbComp layout.service.evaluation.cache.value.Value)
variable (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : layout.zero.val = 0)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (domain : Nat → layout.Request × A → Prop)
    (advanceValid : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ represented original, WeightedCallerHandler.replyMatches layout.service layout.randomBound q represented original →
        WeightedCaller.HeadValid layout.service layout.randomBound domain remaining (advance (c, represented)))
    (admissible : U × layout.service.store.Value → Prop)
    (initialValid : ∀ value, admissible value → WeightedCaller.HeadValid layout.service layout.randomBound domain fuel (initial value.1))
    (initialReserved : ∀ value, admissible value → WeightedOracle.Reserved layout.service layout.terms fuel value.2.val)
    (initialRoom : ∀ value, admissible value → value.2.val.2.1.length + max 1 layout.terms *
      (value.2.val.2.2.1.length + value.2.val.2.2.2.length + 2 * fuel + 1) ≤ layout.service.evaluation.cache.capacityPred + 1)

variable {generatorTime generatorWords drawTime drawWords updateTime updateWords localTime initialTime localWords initialWords extractTime extractWords : Nat}
    {responseTime responseWords : Bool → Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (updateBound : update.BoundedBy updateTime updateWords)
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.service.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))
    (localTimeBound : ∀ value, continuation.time value ≤ localTime)
    (initialTimeBound : ∀ value, initialCode.time value ≤ initialTime)
    (localWordsBound : descriptionWords continuation.code ≤ localWords)
    (initialWordsBound : descriptionWords initialCode.code ≤ initialWords)
    (fallback : layout.extraction.scalar.Value)
    {extract : layout.extraction.input.Value → ProbComp (WeightedCallerFinish.result layout.extraction).Value}
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.RefinesOn layout.extraction.ready layout.port .unit
      layout.extraction.input.representation (WeightedCallerFinish.result layout.extraction).representation extract extractor)
    (extractBound : Interactive.TimeBoundOn layout.extraction.ready layout.port .unit
      layout.extraction.input.representation extractor extractTime)
    (extractStored : (extractor.lower layout.port).descriptionWords ≤ extractWords)

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved initialRoom generatorBound updateBound
  drawTimeBound responseBound localTimeBound initialTimeBound extractCorrect extractBound in
theorem time : Interactive.TimeBoundOn admissible layout.port .unit (input.prod layout.service.store.representation inputFits)
    (program layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
      advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor)
    (timeBudget layout input.encoding.words generatorTime drawTime updateTime responseTime localTime initialTime fuel extractTime) := by
  have invoked := WeightedCaller.refines layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
    combineLaw zeroLaw source uniform drawCorrect domain advance advanceValid layout.state layout.forgery.representation layout.callerFits
    continuation localNameFits input initial initialCode initialNameFits inputFits fuel admissible initialValid initialReserved
  have bounded := WeightedCaller.time layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
    combineLaw zeroLaw source uniform drawCorrect domain advance advanceValid layout.state layout.forgery.representation layout.callerFits
    continuation localNameFits input initial initialCode initialNameFits inputFits generatorBound updateBound drawTimeBound responseBound
    localTimeBound initialTimeBound fuel admissible initialValid initialReserved
  have finished := (WeightedCallerFinish.time_bound layout.extraction layout.config.representation layout.pending layout.exitFits layout.port
    extractCorrect extractBound fallback).viewInput (CallerStep.output layout.control) layout.packetView layout.packet_bytes
  exact bounded.seq invoked finished (called_ready layout generator P comparison correct update updateBuffers updateReserve
    response advance initial fuel source admissible initialReserved initialRoom)

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include generatorBound updateBound drawWordsBound responseBound localWordsBound initialWordsBound extractStored in
theorem words :
    ((program layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
      advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).lower layout.port).descriptionWords ≤
      codeBudget layout input.encoding.words generatorWords drawWords updateWords responseWords localWords initialWords fuel extractWords := by
  have invoked := WeightedCaller.words layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits inputFits
    generatorBound updateBound drawWordsBound responseBound localWordsBound initialWordsBound fuel
  have finished := WeightedCallerFinish.code_bound layout.extraction layout.config.representation layout.pending layout.exitFits layout.port extractStored fallback
  simp only [program, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, codeBudget]
  exact Nat.add_le_add_right (Nat.add_le_add invoked finished) 1

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
theorem names {generatorNamesCount drawNamesCount updateNamesCount responseNamesCount callerSlots : Nat}
    (room : 5 ≤ callerSlots)
    (generatorNames : NamesAccounted generator.program.code generatorNamesCount)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawNamesCount)
    (updateNames : NamesAccounted update.program.code updateNamesCount)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseNamesCount)
    (generatorRoom : generatorNamesCount ≤ callerSlots) (drawRoom : drawNamesCount ≤ callerSlots)
    (updateRoom : updateNamesCount ≤ callerSlots) (responseRoom : responseNamesCount ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots)
    (extractNames : WordIO.NamesAccounted (extractor.lower layout.port) callerSlots) :
    WordIO.NamesAccounted ((program layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
      advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).lower layout.port) callerSlots :=
  (WeightedCaller.names layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits inputFits
    room generatorNames drawNames updateNames responseNames generatorRoom drawRoom updateRoom responseRoom localNames initialNames fuel).seq
    (WeightedCallerFinish.names layout.extraction layout.config.representation layout.pending layout.exitFits layout.port extractNames fallback)

end Signatures.Runtime.CaliperBackend.WeightedCallerExtraction
