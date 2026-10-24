import Proofs.Runtime.Caliper.WeightedCallerExtractionLayout
import Proofs.Runtime.Caliper.WeightedCallerFinishBounds

/-! One generated weighted caller and terminal program. The handler and caller
control are constructed from local routines, and supported caller exits supply
the extractor's capacity precondition through the proved growth invariant. -/
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

def caller : Interactive.Code w :=
  WeightedCaller.program layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits inputFits fuel
def program (fallback : layout.extraction.scalar.Value) (extractor : Interactive.Code w) : Interactive.Code w :=
  .seq (caller layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
    advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel)
    (WeightedCallerFinish.code layout.extraction layout.config.representation layout.pending layout.exitFits fallback extractor)

variable (source : ProbComp layout.service.evaluation.cache.value.Value)
def called (value : U × layout.service.store.Value) : ProbComp layout.Packet :=
  CallerControl.start advance (WeightedCallerHandler.denote layout.service layout.terms layout.termCountFits layout.termStorageFits
    generator layout.randomBound P comparison correct update updateBuffers updateReserve response source) fuel (initial value.1, value.2)
def denote (fallback : layout.extraction.scalar.Value)
    (extract : layout.extraction.input.Value → ProbComp (WeightedCallerFinish.result layout.extraction).Value)
    (value : U × layout.service.store.Value) : ProbComp layout.extraction.scalar.Value :=
  called layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source value >>=
    fun packet => WeightedCallerFinish.denote layout.extraction fallback extract (layout.packetView packet)

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

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include initialReserved in
theorem called_postcondition (value : U × layout.service.store.Value) (valid : admissible value)
    (answer : layout.Packet)
    (reached : answer ∈ support (called layout generator P comparison correct update updateBuffers updateReserve
      response advance initial fuel source value)) : WeightedCaller.Postcondition layout.service layout.terms fuel value.2 answer.2 :=
  WeightedCaller.start_postcondition layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound P comparison correct update updateBuffers updateReserve response source advance fuel
      (initial value.1, value.2) (initialReserved value valid) answer reached

omit [SampleableType (val.Value base)] [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include initialReserved initialRoom in
theorem called_ready (value : U × layout.service.store.Value) (valid : admissible value)
    (answer : layout.Packet)
    (reached : answer ∈ support (called layout generator P comparison correct update updateBuffers updateReserve
      response advance initial fuel source value)) :
    WeightedCallerFinish.ready layout.extraction layout.extraction.ready (layout.packetView answer) :=
  layout.packet_ready (called_postcondition layout generator P comparison correct update updateBuffers updateReserve
    response advance initial fuel source admissible initialReserved value valid answer reached) (initialRoom value valid) answer.1

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved initialRoom in
theorem refines (fallback : layout.extraction.scalar.Value)
    {extract : layout.extraction.input.Value → ProbComp (WeightedCallerFinish.result layout.extraction).Value}
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.RefinesOn layout.extraction.ready layout.port .unit
      layout.extraction.input.representation (WeightedCallerFinish.result layout.extraction).representation extract extractor) :
    Interactive.RefinesOn admissible layout.port .unit (input.prod layout.service.store.representation inputFits)
      layout.extraction.scalar.representation
      (denote layout generator P comparison correct update updateBuffers updateReserve response advance initial fuel source fallback extract)
      (program layout generator P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
        advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor) := by
  have invoked := WeightedCaller.refines layout.service layout.terms layout.termCountFits layout.termStorageFits generator
    layout.randomBound layout.randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve
    combineLaw zeroLaw source uniform drawCorrect domain advance advanceValid layout.state layout.forgery.representation layout.callerFits
    continuation localNameFits input initial initialCode initialNameFits inputFits fuel admissible initialValid initialReserved
  have finished := (WeightedCallerFinish.refines layout.extraction layout.config.representation layout.pending layout.exitFits
    layout.port extractCorrect fallback).viewInput (CallerStep.output layout.control) layout.packetView layout.packet_bytes
  exact invoked.seq finished (called_ready layout generator P comparison correct update updateBuffers updateReserve
    response advance initial fuel source admissible initialReserved initialRoom)

end Signatures.Runtime.CaliperBackend.WeightedCallerExtraction
