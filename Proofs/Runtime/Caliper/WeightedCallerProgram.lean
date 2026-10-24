import Proofs.Runtime.Caliper.WeightedCallerExtractionResources

/-! Complete weighted caller programs contain the constructed extractor. The
`hashes` branch selects scalar hash correction (`true`) or the pair-valued
bad-branch tail (`false`); cutoff returns the supplied scalar default. -/
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

def extractionCode : Interactive.Code w :=
  if hashes then WeightedExtractor.code layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve sum sumBuffers sumReserve layout.port draw
  else WeightedExtractor.badCode layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve layout.port draw

def code : Interactive.Code w :=
  WeightedCallerExtraction.program layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault (extractionCode layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve)

variable (source : ProbComp layout.service.evaluation.cache.value.Value)
def extractionDenote (value : layout.extraction.input.Value) : ProbComp (WeightedCallerFinish.result layout.extraction).Value :=
  if hashes then WeightedExtractor.denote layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve sum source value
  else WeightedExtractor.badDenote layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve source value

def denote : U × layout.service.store.Value → ProbComp layout.extraction.scalar.Value :=
  WeightedCallerExtraction.denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source coefficientDefault (extractionDenote layout generator P comparison correct update updateBuffers updateReserve coefficientDefault hashes extract extractBuffers extractReserve sum source)

omit [DecidableEq (key.Value base)] [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
private theorem ready_bad (value : layout.extraction.input.Value) (ready : layout.extraction.ready value) :
    layout.extraction.badReady value := by
  unfold WeightedExtractor.Layouts.ready at ready
  change value.val.2.1.length + layout.extraction.signing.terms * value.val.2.2.2.length +
    layout.extraction.signing.terms ≤ layout.extraction.signing.rows.accumulation.cache.capacityPred + 1
  omega

variable (drawCorrect : Interactive.Refines layout.port .unit layout.service.evaluation.cache.lookup.unit.representation
    layout.service.evaluation.cache.value.representation (fun _ => source) draw)
omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include drawCorrect in
theorem extraction_refines : Interactive.RefinesOn layout.extraction.ready layout.port .unit
    layout.extraction.input.representation (WeightedCallerFinish.result layout.extraction).representation
    (extractionDenote layout generator P comparison correct update updateBuffers updateReserve coefficientDefault hashes extract extractBuffers extractReserve sum source) (extractionCode layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve) := by
  cases hashes with
  | true => exact WeightedExtractor.refines layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve sum sumBuffers sumReserve layout.port drawCorrect
  | false =>
    have refined := WeightedExtractor.bad_refines layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve layout.port drawCorrect
    exact fun tape value ready before holds => refined tape value (ready_bad layout value ready) before holds

variable    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
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


include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved initialRoom in
theorem refines : Interactive.RefinesOn admissible layout.port .unit (input.prod layout.service.store.representation inputFits)
    layout.extraction.scalar.representation (denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel coefficientDefault hashes extract extractBuffers extractReserve sum source) (code layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve) :=
  WeightedCallerExtraction.refines layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel source drawCorrect combineLaw zeroLaw uniform domain advanceValid
    admissible initialValid initialReserved initialRoom coefficientDefault (extraction_refines layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve source drawCorrect)

end Signatures.Runtime.CaliperBackend.WeightedCallerProgram
