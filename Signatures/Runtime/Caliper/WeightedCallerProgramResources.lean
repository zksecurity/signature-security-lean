import Signatures.Runtime.Caliper.WeightedCallerProgramBounds

/-! The complete caller and extractor share one execution witness for their
source result, elapsed time, and every intermediate memory bound. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerProgram
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerExtraction
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

variable (coefficientDefault : layout.extraction.scalar.Value) (hashes : Bool)
    {calculate : F × (val.Value base × val.Value base) → F}
    (extract : Implementation .unit layout.service.evaluation.combine layout.extraction.scalar calculate)
    {extractSlots : Nat} (extractBuffers : extract.program.code.memBound ≤ extractSlots)
    (extractReserve : extractSlots + 2 < 2 ^ w)
    {numerator : F × val.Value base → F}
    (sum : Implementation .unit layout.extraction.numeratorInput layout.extraction.scalar numerator)
    {sumSlots : Nat} (sumBuffers : sum.program.code.memBound ≤ sumSlots) (sumReserve : sumSlots + 1 < 2 ^ w)

variable (source : ProbComp layout.service.evaluation.cache.value.Value)
    (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
      layout.service.evaluation.cache.value.representation (fun _ => source) draw)
    {generatorTime generatorWords drawTime drawWords updateTime updateWords extractTime extractWords sumTime sumWords : Nat}
    (generatorBound : generator.BoundedBy generatorTime generatorWords)
    (drawTimeBound : Interactive.TimeBound layout.port .unit layout.service.evaluation.cache.lookup.unit.representation draw drawTime)
    (drawWordsBound : (draw.lower layout.port).descriptionWords ≤ drawWords)
    (updateBound : update.BoundedBy updateTime updateWords)
    (extractBound : extract.BoundedBy extractTime extractWords)
    (sumBound : sum.BoundedBy sumTime sumWords)

variable (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
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

variable {responseTime responseWords : Bool → Nat} {localTime initialTime localWords initialWords : Nat}
    (responseBound : ∀ signing, (response signing).BoundedBy (responseTime signing) (responseWords signing))
    (localTimeBound : ∀ value, continuation.time value ≤ localTime)
    (initialTimeBound : ∀ value, initialCode.time value ≤ initialTime)
    (localWordsBound : descriptionWords continuation.code ≤ localWords)
    (initialWordsBound : descriptionWords initialCode.code ≤ initialWords)

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved initialRoom generatorBound updateBound drawTimeBound drawWordsBound responseBound
  localTimeBound initialTimeBound localWordsBound initialWordsBound extractBound sumBound in
theorem resources {generatorNamesCount drawNamesCount updateNamesCount responseNamesCount extractNamesCount sumNamesCount callerSlots : Nat} (room : 5 ≤ callerSlots)
    (generatorNames : NamesAccounted generator.program.code generatorNamesCount)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawNamesCount)
    (updateNames : NamesAccounted update.program.code updateNamesCount)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseNamesCount)
    (generatorRoom : generatorNamesCount ≤ callerSlots) (drawRoom : drawNamesCount ≤ callerSlots)
    (updateRoom : updateNamesCount ≤ callerSlots) (responseRoom : responseNamesCount ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots)
    (extractNames : NamesAccounted extract.program.code extractNamesCount)
    (sumNames : NamesAccounted sum.program.code sumNamesCount)
    (extractionRoom : WeightedExtractor.nameBudget generatorNamesCount drawNamesCount updateNamesCount extractNamesCount sumNamesCount ≤ callerSlots)
    (tape : RandomTape w) (value : U × layout.service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod layout.service.store.representation inputFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((code layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve).execute layout.port .unit tape before)) :
    let code := code layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve
    let elapsed := timeBudget layout hashes input.encoding.words generatorTime drawTime updateTime responseTime localTime initialTime fuel extractTime sumTime
    let stored := codeBudget layout hashes input.encoding.words generatorWords drawWords updateWords responseWords localWords initialWords fuel extractWords sumWords
    finished.time ≤ elapsed ∧ ∃ answer ∈ support (denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel coefficientDefault hashes extract extractBuffers extractReserve sum source value),
      layout.extraction.scalar.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower layout.port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower layout.port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower layout.port).memBound) ∧ between.WellFormed ∧
          ((code.lower layout.port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower layout.port).memBound) ≤
            5 * stored + 4 * callerSlots + registers + 3 * buffers + before.liveMem buffers + elapsed := by
  have refined := refines layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve source drawCorrect combineLaw zeroLaw uniform domain advanceValid
    admissible initialValid initialReserved initialRoom
  have bounded := time layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve source drawCorrect generatorBound drawTimeBound updateBound extractBound sumBound
    combineLaw zeroLaw uniform domain advanceValid admissible initialValid initialReserved initialRoom responseBound localTimeBound initialTimeBound
  have stored := words layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve generatorBound drawWordsBound updateBound extractBound sumBound responseBound localWordsBound initialWordsBound
  have accounted := names layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve room generatorNames drawNames updateNames responseNames extractNames sumNames
    generatorRoom drawRoom updateRoom responseRoom localNames initialNames extractionRoom
  obtain ⟨elapsed, answer, supported, output, execution, memory⟩ := refined.resources bounded stored accounted
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  refine ⟨elapsed, answer, supported, output, execution, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, total⟩ := memory between visited
  exact ⟨regs, bufs, wf, by omega⟩

end Signatures.Runtime.CaliperBackend.WeightedCallerProgram
