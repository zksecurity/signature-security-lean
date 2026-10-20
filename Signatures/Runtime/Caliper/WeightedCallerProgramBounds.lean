import Signatures.Runtime.Caliper.WeightedCallerProgram

/-! Resource formulas for the constructed caller and extractor, derived only
from local code, sampling, and caller contracts. -/
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

def extractionTime (generatorTime drawTime updateTime extractTime sumTime : Nat) : Nat :=
  if hashes then WeightedExtractor.timeBudget layout.extraction generatorTime drawTime updateTime extractTime sumTime
  else WeightedExtractor.badTimeBudget layout.extraction generatorTime drawTime updateTime extractTime

def extractionWords (generatorWords drawWords updateWords extractWords sumWords : Nat) : Nat :=
  if hashes then WeightedExtractor.codeBudget layout.extraction generatorWords drawWords updateWords extractWords sumWords
  else WeightedExtractor.badCodeBudget layout.extraction generatorWords drawWords updateWords extractWords

def timeBudget (inputWords generatorTime drawTime updateTime : Nat) (responseTime : Bool → Nat)
    (localTime initialTime fuel extractTime sumTime : Nat) : Nat :=
  WeightedCallerExtraction.timeBudget layout inputWords generatorTime drawTime updateTime responseTime localTime initialTime fuel
    (extractionTime layout hashes generatorTime drawTime updateTime extractTime sumTime)
def codeBudget (inputWords generatorWords drawWords updateWords : Nat) (responseWords : Bool → Nat)
    (localWords initialWords fuel extractWords sumWords : Nat) : Nat :=
  WeightedCallerExtraction.codeBudget layout inputWords generatorWords drawWords updateWords responseWords localWords initialWords fuel
    (extractionWords layout hashes generatorWords drawWords updateWords extractWords sumWords)

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

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include drawCorrect generatorBound drawTimeBound updateBound extractBound sumBound in
theorem extraction_time : Interactive.TimeBoundOn layout.extraction.ready layout.port .unit layout.extraction.input.representation
    (extractionCode layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve) (extractionTime layout hashes generatorTime drawTime updateTime extractTime sumTime) := by
  cases hashes with
  | true => exact WeightedExtractor.time_bound layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve sum sumBuffers sumReserve layout.port drawCorrect generatorBound drawTimeBound updateBound extractBound sumBound
  | false =>
    have bounded := WeightedExtractor.bad_time_bound layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve layout.port drawCorrect generatorBound drawTimeBound updateBound extractBound
    intro tape value ready before holds finished reached
    apply bounded tape value ?_ before holds finished reached
    unfold WeightedExtractor.Layouts.ready at ready
    change value.val.2.1.length + layout.extraction.signing.terms * value.val.2.2.2.length + layout.extraction.signing.terms ≤ layout.extraction.signing.rows.accumulation.cache.capacityPred + 1
    omega

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include generatorBound drawWordsBound updateBound extractBound sumBound in
theorem extraction_words : ((extractionCode layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve).lower layout.port).descriptionWords ≤
    extractionWords layout hashes generatorWords drawWords updateWords extractWords sumWords := by
  cases hashes with
  | true => exact WeightedExtractor.code_bound layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve sum sumBuffers sumReserve layout.port generatorBound updateBound extractBound sumBound draw drawWordsBound
  | false => exact WeightedExtractor.bad_code_bound layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve layout.port generatorBound updateBound extractBound draw drawWordsBound

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
theorem extraction_names {generatorNamesCount drawNamesCount updateNamesCount extractNamesCount sumNamesCount : Nat}
    (generatorNames : NamesAccounted generator.program.code generatorNamesCount)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawNamesCount)
    (updateNames : NamesAccounted update.program.code updateNamesCount)
    (extractNames : NamesAccounted extract.program.code extractNamesCount)
    (sumNames : NamesAccounted sum.program.code sumNamesCount) :
    WordIO.NamesAccounted ((extractionCode layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve).lower layout.port)
      (WeightedExtractor.nameBudget generatorNamesCount drawNamesCount updateNamesCount extractNamesCount sumNamesCount) := by
  cases hashes with
  | true => exact WeightedExtractor.names layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve sum sumBuffers sumReserve layout.port draw generatorNames drawNames updateNames extractNames sumNames
  | false =>
    exact (WeightedExtractor.bad_names layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve layout.port draw generatorNames drawNames updateNames extractNames).mono
      (by unfold WeightedExtractor.nameBudget; omega)

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
theorem extraction_descriptionFits {generatorSlots drawSlots : Nat}
    (generatorBuffers : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 3 < 2 ^ w)
    (drawFits : (draw.lower layout.port).DescriptionFits) (drawNames : WordIO.NamesBound (draw.lower layout.port) drawSlots)
    (drawReserve : drawSlots + 5 < 2 ^ w) (updateWidth : updateSlots + 4 < 2 ^ w) :
    ((extractionCode layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve).lower layout.port).DescriptionFits := by
  cases hashes with
  | true => exact WeightedExtractor.descriptionFits layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve sum sumBuffers sumReserve layout.port draw generatorBuffers generatorReserve drawFits drawNames drawReserve updateWidth
  | false => exact WeightedExtractor.bad_descriptionFits layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve layout.port draw generatorBuffers generatorReserve drawFits drawNames drawReserve updateWidth

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

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved initialRoom
  generatorBound drawTimeBound updateBound extractBound sumBound responseBound localTimeBound initialTimeBound in
theorem time : Interactive.TimeBoundOn admissible layout.port .unit (input.prod layout.service.store.representation inputFits)
    (code layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve)
    (timeBudget layout hashes input.encoding.words generatorTime drawTime updateTime responseTime localTime initialTime fuel extractTime sumTime) :=
  WeightedCallerExtraction.time layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel source drawCorrect combineLaw zeroLaw uniform domain advanceValid
    admissible initialValid initialReserved initialRoom generatorBound updateBound drawTimeBound responseBound localTimeBound initialTimeBound
    coefficientDefault (extraction_refines layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve source drawCorrect)
    (extraction_time layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve source drawCorrect generatorBound drawTimeBound updateBound extractBound sumBound)

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include generatorBound drawWordsBound updateBound extractBound sumBound responseBound localWordsBound initialWordsBound in
theorem words : ((code layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve).lower layout.port).descriptionWords ≤
    codeBudget layout hashes input.encoding.words generatorWords drawWords updateWords responseWords localWords initialWords fuel extractWords sumWords :=
  WeightedCallerExtraction.words layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel generatorBound updateBound drawWordsBound responseBound localWordsBound initialWordsBound
    coefficientDefault (extraction_words layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve generatorBound drawWordsBound updateBound extractBound sumBound)

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
theorem names {generatorNamesCount drawNamesCount updateNamesCount responseNamesCount extractNamesCount sumNamesCount callerSlots : Nat}
    (room : 5 ≤ callerSlots)
    (generatorNames : NamesAccounted generator.program.code generatorNamesCount)
    (drawNames : WordIO.NamesBound (draw.lower layout.port) drawNamesCount)
    (updateNames : NamesAccounted update.program.code updateNamesCount)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseNamesCount)
    (extractNames : NamesAccounted extract.program.code extractNamesCount)
    (sumNames : NamesAccounted sum.program.code sumNamesCount)
    (generatorRoom : generatorNamesCount ≤ callerSlots) (drawRoom : drawNamesCount ≤ callerSlots)
    (updateRoom : updateNamesCount ≤ callerSlots) (responseRoom : responseNamesCount ≤ callerSlots)
    (localNames : NamesAccounted continuation.code callerSlots) (initialNames : NamesAccounted initialCode.code callerSlots)
    (extractionRoom : WeightedExtractor.nameBudget generatorNamesCount drawNamesCount updateNamesCount extractNamesCount sumNamesCount ≤ callerSlots) :
    WordIO.NamesAccounted ((code layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve).lower layout.port) callerSlots :=
  WeightedCallerExtraction.names layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault room generatorNames drawNames updateNames responseNames
    generatorRoom drawRoom updateRoom responseRoom localNames initialNames
    ((extraction_names layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve generatorNames drawNames updateNames extractNames sumNames).mono extractionRoom)

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include generatorBound drawWordsBound updateBound responseBound in
theorem descriptionFits {generatorSlots generatorNamesCount drawNamesCount updateNamesCount responseNamesCount : Nat}
    (generatorBuffers : generator.program.code.memBound ≤ generatorSlots) (generatorReserve : generatorSlots + 3 < 2 ^ w)
    (generatorNames : NamesAccounted generator.program.code generatorNamesCount)
    (drawFits : (draw.lower layout.port).DescriptionFits) (drawNames : WordIO.NamesBound (draw.lower layout.port) drawNamesCount)
    (drawReserve : drawNamesCount + 5 < 2 ^ w) (updateWidth : updateSlots + 4 < 2 ^ w)
    (updateNames : NamesAccounted update.program.code updateNamesCount)
    (responseNames : ∀ signing, NamesAccounted (response signing).program.code responseNamesCount)
    (handlerReserve : WeightedOracle.namesBudget generatorNamesCount drawNamesCount updateNamesCount responseNamesCount +
      WeightedCallerHandler.codeBudget layout.service layout.terms layout.termCountFits layout.termStorageFits
        layout.randomBound layout.randomFits generatorWords drawWords updateWords responseWords + 1 < 2 ^ w) :
    ((code layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve).lower layout.port).DescriptionFits :=
  WeightedCallerExtraction.descriptionFits layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel generatorBound updateBound drawWordsBound responseBound coefficientDefault
    generatorBuffers (by omega) generatorNames drawFits drawNames (by omega) updateNames responseNames handlerReserve
    (extraction_descriptionFits layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve generatorBuffers generatorReserve drawFits drawNames drawReserve updateWidth)

end Signatures.Runtime.CaliperBackend.WeightedCallerProgram
