import Proofs.Runtime.Caliper.WeightedCallerProgram
import Proofs.Runtime.Caliper.WeightedCallerExtractionSource
import Proofs.Runtime.Caliper.WeightedExtractorSource

/-! Erasing the complete weighted program recovers the original caller oracle
and private-list extraction, including the same lazily sampled cache. Only local
caller correspondence and primitive algebraic/sampling laws are assumptions. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerProgram
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerExtraction Model.LazyAGM
open BLS.LazyAGM.Reduction (privateListOracle)

abbrev ExtractionInput (K M G F R : Type) :=
  (M × (F × (List F × List F))) × (List (K × R) × Transcript K M G)

noncomputable def extractionSource {K M G F R : Type} [DecidableEq K]
    [Semiring F] [SampleableType R] [AddCommMonoid R] [Module F R]
    (hashes : Bool) (terms : M → List (K × F))
    (numerator : F × R → F) (calculate : F × (R × R) → F)
    (value : ExtractionInput K M G F R) : ProbComp (F × List (K × R)) :=
  if hashes then do
    let hashed ← (simulateQ privateListOracle
      (evalTerms (BLS.LazyAGM.Reduction.traceTerms value.1.2.2.1 value.2.2.1.reverse))).run value.2.1
    let signed ← (simulateQ privateListOracle
      (evalTerms (WeightedReduction.signedTerms terms value.1.2.2.2 value.2.2.2.reverse))).run hashed.2
    (fun target => (calculate (numerator (value.1.2.1, hashed.1), target.1, signed.1), target.2)) <$>
      (simulateQ privateListOracle (evalTerms (terms value.1.1))).run signed.2
  else do
    let signed ← (simulateQ privateListOracle
      (evalTerms (WeightedReduction.signedTerms terms value.1.2.2.2 value.2.2.2.reverse))).run value.2.1
    (fun target => (calculate (value.1.2.1, target.1, signed.1), target.2)) <$>
      (simulateQ privateListOracle (evalTerms (terms value.1.1))).run signed.2

variable {w : Nat} {C G F M A U : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [Semiring F] [Module F (val.Value base)]
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
    (coefficientLaw : coefficientDefault.val = 0)
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

include combineLaw zeroLaw coefficientLaw uniform in
theorem extraction_source (value : layout.extraction.input.Value) (ready : layout.extraction.ready value) :
    Subtype.val <$> extractionDenote layout generator P comparison correct update updateBuffers updateReserve coefficientDefault hashes extract extractBuffers extractReserve sum source value =
      extractionSource hashes generate numerator calculate value.val := by
  cases hashes with
  | true => exact WeightedExtractor.denote_source layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve sum combineLaw zeroLaw coefficientLaw source uniform value ready
  | false =>
    apply WeightedExtractor.bad_denote_source layout.extraction coefficientDefault layout.zero layout.default generator P comparison correct update updateBuffers updateReserve extract extractBuffers extractReserve combineLaw zeroLaw coefficientLaw source uniform value
    unfold WeightedExtractor.Layouts.ready at ready
    change value.val.2.1.length + layout.extraction.signing.terms * value.val.2.2.2.length +
      layout.extraction.signing.terms ≤ layout.extraction.signing.rows.accumulation.cache.capacityPred + 1
    omega

include combineLaw zeroLaw coefficientLaw uniform in
theorem extraction_scalar_source (value : layout.extraction.input.Value) (ready : layout.extraction.ready value) :
    (fun answer => answer.val.1) <$> extractionDenote layout generator P comparison correct update updateBuffers updateReserve coefficientDefault hashes extract extractBuffers extractReserve sum source value =
      Prod.fst <$> extractionSource hashes generate numerator calculate value.val := by
  have equality := congrArg (fun computation => Prod.fst <$> computation)
    (extraction_source layout generator P comparison correct update updateBuffers updateReserve coefficientDefault hashes extract extractBuffers extractReserve sum source
      coefficientLaw combineLaw zeroLaw uniform value ready)
  simpa only [Functor.map_map] using equality

variable {V : Type}
    (machine : OracleMachine (Model.LazyAGM.advSpec (key.Value base) M G) V layout.forgery.Value)
    (stateView : layout.Request × A → machine.State) (inputView : U → V)
    (advanceMatches : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ next : (Model.LazyAGM.advSpec (key.Value base) M G).Range
          (WeightedCallerHandler.query layout.service layout.randomBound q) → machine.State,
        machine.view (stateView (q, c)) = .inr ⟨WeightedCallerHandler.query layout.service layout.randomBound q, next⟩ →
        ∀ represented original, WeightedCallerHandler.replyMatches layout.service layout.randomBound q represented original →
          CallerMachine.Matches machine (WeightedCallerHandler.query layout.service layout.randomBound) stateView
            (advance (c, represented)) (next original))
    (initialMatches : ∀ value, admissible value →
      CallerMachine.Matches machine (WeightedCallerHandler.query layout.service layout.randomBound) stateView
        (initial value.1) (machine.init (inputView value.1)))

include combineLaw zeroLaw coefficientLaw uniform advanceValid initialValid initialReserved initialRoom advanceMatches initialMatches in
theorem denote_source
    (sourceProgram : V → OracleComp (advSpec (key.Value base) M G) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (value : U × layout.service.store.Value) (valid : admissible value) :
    Subtype.val <$> denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel coefficientDefault hashes extract extractBuffers extractReserve sum source value =
      ((simulateQ (WeightedCallerHandler.original generate respond) (sourceProgram (inputView value.1))).run value.2.val >>=
        fun answer => Prod.fst <$> extractionSource hashes generate numerator calculate (answer.1.val, answer.2.2)) :=
  WeightedCallerExtraction.denote_source layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source combineLaw zeroLaw uniform domain advanceValid
    admissible initialValid initialReserved initialRoom coefficientDefault (extractionDenote layout generator P comparison correct update updateBuffers updateReserve coefficientDefault hashes extract extractBuffers extractReserve sum source)
    (fun value => Prod.fst <$> extractionSource hashes generate numerator calculate value)
    (extraction_scalar_source layout generator P comparison correct update updateBuffers updateReserve coefficientDefault hashes extract extractBuffers extractReserve sum source coefficientLaw combineLaw zeroLaw uniform)
    machine stateView inputView advanceMatches initialMatches sourceProgram implements value valid

include drawCorrect combineLaw zeroLaw coefficientLaw uniform advanceValid initialValid initialReserved initialRoom advanceMatches initialMatches in
theorem observe_source
    (sourceProgram : V → OracleComp (advSpec (key.Value base) M G) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (tape : RandomTape w) (value : U × layout.service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod layout.service.store.representation inputFits).Holds value before) :
    (fun finished => Subtype.val <$> Interactive.observe layout.extraction.scalar.representation finished) <$>
        (code layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve).execute layout.port .unit tape before =
      some <$> ((simulateQ (WeightedCallerHandler.original generate respond) (sourceProgram (inputView value.1))).run value.2.val >>=
        fun answer => Prod.fst <$> extractionSource hashes generate numerator calculate (answer.1.val, answer.2.2)) :=
  WeightedCallerExtraction.observe_source layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel source drawCorrect combineLaw zeroLaw uniform domain advanceValid
    admissible initialValid initialReserved initialRoom coefficientDefault (extractionDenote layout generator P comparison correct update updateBuffers updateReserve coefficientDefault hashes extract extractBuffers extractReserve sum source)
    (fun value => Prod.fst <$> extractionSource hashes generate numerator calculate value)
    (extraction_scalar_source layout generator P comparison correct update updateBuffers updateReserve coefficientDefault hashes extract extractBuffers extractReserve sum source coefficientLaw combineLaw zeroLaw uniform)
    machine stateView inputView advanceMatches initialMatches (extraction_refines layout generator P comparison correct update updateBuffers updateReserve draw coefficientDefault hashes extract extractBuffers extractReserve sum sumBuffers sumReserve source drawCorrect)
    sourceProgram implements tape value valid before holds

end Signatures.Runtime.CaliperBackend.WeightedCallerProgram
