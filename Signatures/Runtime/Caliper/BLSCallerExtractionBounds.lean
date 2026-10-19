import Signatures.Runtime.Caliper.BLSCallerExtraction

/-! Composed caller/extraction costs. The caller and terminal budgets are
proved from their actual component programs, including unrolled caller code,
all routing, and the retained private state. -/
namespace Signatures.Runtime.CaliperBackend.BLSCallerExtraction
open Caliper BoundedSource OracleComp OracleSpec
variable {w : Nat} {C G F A U : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (layout : Layouts w (key.Value base) G F (val.Value base) C A)
    (default : layout.service.cache.value.Value)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit layout.service.responseInput layout.service.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (draw : Interactive.Code w)
    (advance : A × layout.Reply → layout.forgery.Value ⊕ (layout.Request × A))
    (continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → layout.forgery.Value ⊕ (layout.Request × A))
    (initialCode : Realizer .unit input (CallerStep.next layout.control) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.service.store.representation.encoding.words < 2 ^ w)
    (fuel : Nat)


def timeBudget (inputWords drawTime : Nat) (responseTime : Bool → Nat)
    (localTime initialTime fuel extractTime : Nat) : Nat :=
  BLSCaller.timeBudget layout.service inputWords (CallerStep.width layout.control) drawTime responseTime localTime initialTime fuel +
    BLSCallerFinish.timeBudget layout.extraction layout.config.representation layout.pending layout.exitFits extractTime
def codeBudget (inputWords drawWords : Nat) (responseWords : Bool → Nat)
    (localWords initialWords fuel extractWords : Nat) : Nat :=
  BLSCaller.codeBudget layout.service inputWords (CallerStep.width layout.control) drawWords responseWords localWords initialWords fuel +
    BLSCallerFinish.codeBudget layout.extraction layout.config.representation layout.pending layout.exitFits extractWords + 1

variable (drawSource : ProbComp layout.service.cache.value.Value)
variable (drawCorrect : Interactive.Refines layout.port .unit layout.service.cache.lookup.unit.representation layout.service.cache.value.representation
      (fun _ => drawSource) draw)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (domain : Nat → layout.Request × A → Prop)
    (advanceValid : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ represented original, BLSCallerHandler.replyMatches layout.service layout.randomBound q represented original →
        BLSCaller.HeadValid layout.service layout.randomBound domain remaining (advance (c, represented)))
    (admissible : U × layout.service.store.Value → Prop)
    (initialValid : ∀ value, admissible value → BLSCaller.HeadValid layout.service layout.randomBound domain fuel (initial value.1))
    (initialReserved : ∀ value, admissible value → BLSReply.Reserved layout.service fuel value.2.val)
    (initialRoom : ∀ value, admissible value → value.2.val.2.1.length + value.2.val.2.2.1.length +
      value.2.val.2.2.2.length + 2 * fuel + 1 ≤ layout.service.cache.capacityPred + 1)


variable {drawTime drawWords localTime initialTime localWords initialWords extractTime extractWords : Nat}
    {responseTime responseWords : Bool → Nat}
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.service.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))
    (localTimeBound : ∀ value, continuation.time value ≤ localTime)
    (initialTimeBound : ∀ value, initialCode.time value ≤ initialTime)
    (localWordsBound : descriptionWords continuation.code ≤ localWords)
    (initialWordsBound : descriptionWords initialCode.code ≤ initialWords)
    (fallback : layout.extraction.rows.accumulation.coefficient.Value)
    {extract : (BLSExtractorFrame.input layout.extraction).Value → ProbComp (BLSCallerFinish.result layout.extraction).Value}
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.RefinesOn (BLSExtractorFrame.ready layout.extraction) layout.port .unit
      (BLSExtractorFrame.input layout.extraction).representation (BLSCallerFinish.result layout.extraction).representation extract extractor)
    (extractBound : Interactive.TimeBoundOn (BLSExtractorFrame.ready layout.extraction) layout.port .unit
      (BLSExtractorFrame.input layout.extraction).representation extractor extractTime)
    (extractStored : (extractor.lower layout.port).descriptionWords ≤ extractWords)

include drawCorrect drawLaw advanceValid initialValid initialReserved initialRoom drawTimeBound responseBound
  localTimeBound initialTimeBound extractCorrect extractBound in
theorem time : Interactive.TimeBoundOn admissible layout.port .unit (input.prod layout.service.store.representation inputFits)
    (program layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor)
    (timeBudget layout input.encoding.words drawTime responseTime localTime initialTime fuel extractTime) := by
  have invoked := BLSCaller.refines layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve
    draw drawSource drawCorrect drawLaw domain advance advanceValid layout.state layout.forgery.representation layout.callerFits continuation localNameFits
    input initial initialCode initialNameFits inputFits fuel admissible initialValid initialReserved
  have callerBound := BLSCaller.time layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve
    draw drawSource drawCorrect drawLaw domain advance advanceValid layout.state layout.forgery.representation layout.callerFits continuation localNameFits
    input initial initialCode initialNameFits inputFits drawTimeBound responseBound localTimeBound initialTimeBound fuel admissible initialValid initialReserved
  have finishBound := (BLSCallerFinish.time_bound layout.extraction layout.config.representation layout.pending layout.exitFits layout.port
    extractCorrect extractBound fallback).viewInput (CallerStep.output layout.control) layout.packetView layout.packet_bytes
  exact Interactive.TimeBoundOn.seq invoked callerBound finishBound (called_ready layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource drawLaw
    admissible initialReserved initialRoom)

omit [SampleableType (val.Value base)] in
include drawWordsBound responseBound localWordsBound initialWordsBound extractStored in
theorem words :
    ((program layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).lower layout.port).descriptionWords ≤
      codeBudget layout input.encoding.words drawWords responseWords localWords initialWords fuel extractWords := by
  have callerBound := BLSCaller.words layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve
    draw advance layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits inputFits
    drawWordsBound responseBound localWordsBound initialWordsBound fuel
  have finishBound := BLSCallerFinish.code_bound layout.extraction layout.config.representation layout.pending layout.exitFits layout.port extractStored fallback
  simp only [program, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, codeBudget]
  exact Nat.add_le_add_right (Nat.add_le_add callerBound finishBound) 1

omit [SampleableType (val.Value base)] in
theorem names {drawSlots responseSlots callerSlots : Nat} (room : 5 ≤ callerSlots)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawSlots)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseSlots)
    (drawRoom : drawSlots ≤ callerSlots) (responseRoom : responseSlots ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots)
    (extractNames : WordIO.NamesAccounted (extractor.lower layout.port) callerSlots) :
    WordIO.NamesAccounted ((program layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).lower layout.port) callerSlots :=
  (BLSCaller.names layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve draw advance
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits inputFits
    room drawNames responseNames drawRoom responseRoom localNames initialNames fuel).seq
    (BLSCallerFinish.names layout.extraction layout.config.representation layout.pending layout.exitFits layout.port extractNames fallback)

end Signatures.Runtime.CaliperBackend.BLSCallerExtraction
