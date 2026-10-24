import Proofs.Runtime.Caliper.BLSCallerExtractionBounds

/-! Whole-memory accounting and accepted stored operands of the composed
caller and extractor. The handler's saved-buffer name is derived from its
constructed code budget and primitive name reservation. -/
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


include drawCorrect drawLaw advanceValid initialValid initialReserved initialRoom drawTimeBound drawWordsBound responseBound
  localTimeBound initialTimeBound localWordsBound initialWordsBound extractCorrect extractBound extractStored in
theorem resources {drawSlots responseSlots callerSlots : Nat} (room : 5 ≤ callerSlots)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawSlots)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseSlots)
    (drawRoom : drawSlots ≤ callerSlots) (responseRoom : responseSlots ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots)
    (extractNames : WordIO.NamesAccounted (extractor.lower layout.port) callerSlots)
    (tape : RandomTape w) (value : U × layout.service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod layout.service.store.representation inputFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).execute layout.port .unit tape before)) :
    let code := program layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor
    let elapsed := timeBudget layout input.encoding.words drawTime responseTime localTime initialTime fuel extractTime
    let stored := codeBudget layout input.encoding.words drawWords responseWords localWords initialWords fuel extractWords
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (denote layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource fallback extract value),
      layout.extraction.rows.accumulation.coefficient.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower layout.port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower layout.port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower layout.port).memBound) ∧ between.WellFormed ∧
          ((code.lower layout.port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower layout.port).memBound) ≤
            5 * stored + 4 * callerSlots + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have refined := refines layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel drawSource drawCorrect drawLaw domain advanceValid admissible initialValid initialReserved initialRoom fallback extractCorrect
  have bounded := time layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel drawSource drawCorrect drawLaw domain advanceValid admissible initialValid initialReserved initialRoom drawTimeBound responseBound localTimeBound initialTimeBound fallback extractCorrect extractBound
  have stored := words layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel drawWordsBound responseBound localWordsBound initialWordsBound fallback extractStored
  have accounted := names layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback room drawNames responseNames drawRoom responseRoom localNames initialNames extractNames
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored accounted
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩

omit [SampleableType (val.Value base)] in
include drawWordsBound responseBound in
theorem descriptionFits {drawSlots responseSlots : Nat}
    (drawFits : (draw.lower layout.port).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawSlots)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseSlots)
    (handlerReserve : max (max 5 drawSlots) responseSlots +
      (BLSOracle.codeBudget layout.service (BLSDispatch.codeBudget layout.service drawWords responseWords) +
        710 * BLSCallerPackets.width layout.service + 420) + 1 < 2 ^ w)
    (extractFits : (extractor.lower layout.port).DescriptionFits) :
    ((program layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).lower layout.port).DescriptionFits := by
  have stored := BLSCallerHandler.words layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve draw drawWordsBound responseBound
  have named := BLSCallerHandler.names layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve draw drawNames responseNames
  have savedFit : Interactive.savedBuffer layout.port (BLSCallerHandler.code layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve draw) < 2 ^ w := by
    have bound := named.buffers
    change ((BLSCallerHandler.code layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve draw).lower layout.port).memBound ≤
      max (max 5 drawSlots) responseSlots +
        ((BLSCallerHandler.code layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve draw).lower layout.port).descriptionWords at bound
    change ((BLSCallerHandler.code layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve draw).lower layout.port).descriptionWords ≤ _ at stored
    dsimp only [Interactive.savedBuffer]
    omega
  have invoked := BLSCaller.descriptionFits layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve draw advance
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits inputFits
    drawFits drawNames (by omega) savedFit fuel
  exact .seq layout.service.cache.wordFits invoked
    (BLSCallerFinish.descriptionFits layout.extraction layout.config.representation layout.pending layout.exitFits layout.port fallback extractFits)
end Signatures.Runtime.CaliperBackend.BLSCallerExtraction
