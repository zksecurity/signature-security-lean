import Signatures.Runtime.Caliper.BLSCallerExtractionLayout
import Signatures.Runtime.Caliper.BLSCallerFinishBounds

/-! The generated BLS caller followed by executed terminal handling. The caller
and handler code are constructed from local initialization/continuation and
response routines. The caller's growth proof supplies extraction readiness for
every supported exit; no completed-caller invariant is assumed. -/
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

def caller : Interactive.Code w :=
  BLSCaller.program layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve draw advance
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits inputFits fuel
def program (fallback : layout.extraction.rows.accumulation.coefficient.Value) (extractor : Interactive.Code w) : Interactive.Code w :=
  .seq (caller layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel)
    (BLSCallerFinish.code layout.extraction layout.config.representation layout.pending layout.exitFits fallback extractor)

variable (drawSource : ProbComp layout.service.cache.value.Value)
def called (value : U × layout.service.store.Value) : ProbComp layout.Packet :=
  CallerControl.start advance (BLSCallerHandler.denote layout.service default layout.randomBound P comparison correct response responseBuffers reserve drawSource)
    fuel (initial value.1, value.2)
def denote (fallback : layout.extraction.rows.accumulation.coefficient.Value)
    (extract : (BLSExtractorFrame.input layout.extraction).Value → ProbComp (BLSCallerFinish.result layout.extraction).Value)
    (value : U × layout.service.store.Value) : ProbComp layout.extraction.rows.accumulation.coefficient.Value :=
  called layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource value >>=
    fun packet => BLSCallerFinish.denote layout.extraction fallback extract (layout.packetView packet)

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

include drawLaw initialReserved initialRoom in
theorem called_ready (value : U × layout.service.store.Value) (valid : admissible value)
    (answer : layout.Packet)
    (reached : answer ∈ support (called layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource value)) :
    BLSCallerFinish.ready layout.extraction (BLSExtractorFrame.ready layout.extraction) (layout.packetView answer) := by
  have post := BLSCaller.start_postcondition layout.service default layout.randomBound P comparison correct response responseBuffers reserve
    drawSource drawLaw advance fuel (initial value.1, value.2) (initialReserved value valid) answer reached
  exact layout.packet_ready post (initialRoom value valid) answer.1

include drawCorrect drawLaw advanceValid initialValid initialReserved initialRoom in
theorem refines (fallback : layout.extraction.rows.accumulation.coefficient.Value)
    {extract : (BLSExtractorFrame.input layout.extraction).Value → ProbComp (BLSCallerFinish.result layout.extraction).Value}
    {extractor : Interactive.Code w}
    (extractCorrect : Interactive.RefinesOn (BLSExtractorFrame.ready layout.extraction) layout.port .unit
      (BLSExtractorFrame.input layout.extraction).representation (BLSCallerFinish.result layout.extraction).representation extract extractor) :
    Interactive.RefinesOn admissible layout.port .unit (input.prod layout.service.store.representation inputFits)
      layout.extraction.rows.accumulation.coefficient.representation
      (denote layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource fallback extract)
      (program layout default P comparison correct response responseBuffers reserve draw advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel fallback extractor) := by
  have invoked := BLSCaller.refines layout.service default layout.randomBound layout.randomFits P comparison correct response responseBuffers reserve
    draw drawSource drawCorrect drawLaw domain advance advanceValid layout.state layout.forgery.representation layout.callerFits continuation localNameFits
    input initial initialCode initialNameFits inputFits fuel admissible initialValid initialReserved
  have finished := (BLSCallerFinish.refines layout.extraction layout.config.representation layout.pending layout.exitFits layout.port extractCorrect fallback).viewInput
    (CallerStep.output layout.control) layout.packetView layout.packet_bytes
  exact invoked.seq finished (called_ready layout default P comparison correct response responseBuffers reserve advance initial fuel drawSource drawLaw
    admissible initialReserved initialRoom)
end Signatures.Runtime.CaliperBackend.BLSCallerExtraction
