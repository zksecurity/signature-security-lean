import Proofs.Runtime.Caliper.WeightedCallerExtractionBounds

/-! Whole-memory and operand-width proofs for caller execution followed by
extraction. The handler reservation is derived from its constructed code. -/
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

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved initialRoom generatorBound updateBound drawTimeBound drawWordsBound responseBound
  localTimeBound initialTimeBound localWordsBound initialWordsBound extractCorrect extractBound extractStored in
theorem resources {generatorNamesCount drawNamesCount updateNamesCount responseNamesCount callerSlots : Nat} (room : 5 ≤ callerSlots)
    (generatorNames : NamesAccounted generator.program.code generatorNamesCount)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawNamesCount)
    (updateNames : NamesAccounted update.program.code updateNamesCount)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseNamesCount)
    (generatorRoom : generatorNamesCount ≤ callerSlots) (drawRoom : drawNamesCount ≤ callerSlots)
    (updateRoom : updateNamesCount ≤ callerSlots) (responseRoom : responseNamesCount ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots)
    (extractNames : WordIO.NamesAccounted (extractor.lower layout.port) callerSlots)
    (tape : RandomTape w) (value : U × layout.service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod layout.service.store.representation inputFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).execute layout.port .unit tape before)) :
    let code := program layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor
    let elapsed := timeBudget layout input.encoding.words generatorTime drawTime updateTime responseTime localTime initialTime fuel extractTime
    let stored := codeBudget layout input.encoding.words generatorWords drawWords updateWords responseWords localWords initialWords fuel extractWords
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source fallback extract value),
      layout.extraction.scalar.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower layout.port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower layout.port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower layout.port).memBound) ∧ between.WellFormed ∧
          ((code.lower layout.port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower layout.port).memBound) ≤
            5 * stored + 4 * callerSlots + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have refined := refines layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel source drawCorrect combineLaw zeroLaw uniform domain advanceValid admissible initialValid initialReserved initialRoom fallback extractCorrect
  have bounded := time layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel source drawCorrect combineLaw zeroLaw uniform domain advanceValid admissible initialValid initialReserved initialRoom generatorBound updateBound drawTimeBound responseBound localTimeBound initialTimeBound fallback extractCorrect extractBound
  have stored := words layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel generatorBound updateBound drawWordsBound responseBound localWordsBound initialWordsBound fallback extractStored
  have accounted := names layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback room generatorNames drawNames updateNames responseNames generatorRoom drawRoom updateRoom responseRoom localNames initialNames extractNames
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored accounted
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include generatorBound updateBound drawWordsBound responseBound in
theorem descriptionFits {generatorSlots generatorNamesCount drawNamesCount updateNamesCount responseNamesCount : Nat}
    (generatorBuffers : generator.program.code.memBound ≤ generatorSlots)
    (generatorReserve : generatorSlots + 1 < 2 ^ w)
    (generatorNames : NamesAccounted generator.program.code generatorNamesCount)
    (drawFits : (draw.lower layout.port).DescriptionFits)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawNamesCount)
    (drawReserve : drawNamesCount + 3 < 2 ^ w)
    (updateNames : NamesAccounted update.program.code updateNamesCount)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseNamesCount)
    (handlerReserve : WeightedOracle.namesBudget generatorNamesCount drawNamesCount updateNamesCount responseNamesCount +
      WeightedCallerHandler.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits
        layout.randomBound layout.randomFits generatorWords drawWords updateWords responseWords + 1 < 2 ^ w)
    (extractFits : (extractor.lower layout.port).DescriptionFits) :
    ((program layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
      advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor).lower layout.port).DescriptionFits := by
  have stored := WeightedCallerHandler.code_bound layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
    generatorBound drawWordsBound updateBound responseBound
  have named := WeightedCallerHandler.names layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
    generatorNames drawNames updateNames responseNames
  have savedFit : Interactive.savedBuffer layout.port (WeightedCallerHandler.code layout.service layout.terms layout.termCountFits
      layout.termStorageFits generator layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve
      draw response responseBuffers responseReserve) < 2 ^ w := by
    have bound := named.buffers
    change ((WeightedCallerHandler.code layout.service layout.terms layout.termCountFits layout.termStorageFits generator
      layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve).lower layout.port).memBound ≤
      WeightedOracle.namesBudget generatorNamesCount drawNamesCount updateNamesCount responseNamesCount +
      ((WeightedCallerHandler.code layout.service layout.terms layout.termCountFits layout.termStorageFits generator
        layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve).lower layout.port).descriptionWords at bound
    change ((WeightedCallerHandler.code layout.service layout.terms layout.termCountFits layout.termStorageFits generator
      layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve).lower layout.port).descriptionWords ≤ _ at stored
    have minimum : 5 ≤ WeightedOracle.namesBudget generatorNamesCount drawNamesCount updateNamesCount responseNamesCount := by
      unfold WeightedOracle.namesBudget
      omega
    dsimp only [Interactive.savedBuffer]
    omega
  have invoked := WeightedCaller.descriptionFits layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits inputFits
    generatorBuffers generatorReserve drawFits drawNames drawReserve savedFit fuel
  exact .seq layout.service.evaluation.cache.wordFits invoked
    (WeightedCallerFinish.descriptionFits layout.extraction layout.config.representation layout.pending layout.exitFits layout.port fallback extractFits)
end Signatures.Runtime.CaliperBackend.WeightedCallerExtraction
