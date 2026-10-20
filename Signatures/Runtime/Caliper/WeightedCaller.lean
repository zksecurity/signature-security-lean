import Signatures.Runtime.Caliper.WeightedCallerInvariant
import Signatures.Runtime.Caliper.WeightedCallerSource
import Signatures.Runtime.Caliper.CallerExecution

/-! Assemble a complete weighted caller from actual local initialization and
continuation code. The weighted handler, packet conversion and control flow are
constructed here; their correctness is not an input. Local caller invariants
need only be preserved for replies matching the pending typed source query. -/

namespace Signatures.Runtime.CaliperBackend.WeightedCaller
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets

section Layouts
variable {w : Nat} {K M F R C G A B : Type} (service : WeightedOracle.Layouts w K M F R C G)
    (capacity : Nat) (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    (state : Representation w A) (result : Representation w B)
    (fits : 8 * (1 + state.encoding.words + (request service randomBound randomFits).encoding.words +
      (reply service randomBound randomFits).encoding.words + result.encoding.words + service.store.representation.encoding.words) < 2 ^ w)

def layout : CallerStep.Layouts w A (Request service randomBound) (Reply service randomBound) B service.store.Value :=
  ⟨state, request service randomBound randomFits, reply service randomBound randomFits,
    result, service.store.representation, fits, service.evaluation.cache.wordFits⟩

def HeadValid (domain : Nat → Request service randomBound × A → Prop) (remaining : Nat)
    (head : B ⊕ (Request service randomBound × A)) : Prop :=
  match head with | .inl _ => True | .inr pending => domain remaining pending

def Invariant (domain : Nat → Request service randomBound × A → Prop) (remaining : Nat)
    (value : CallerControl.Frame A (Request service randomBound) service.store.Value) : Prop :=
  domain remaining value.1 ∧ WeightedOracle.Reserved service capacity remaining value.2.val

end Layouts

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {M F C G A B U : Type}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    [AddCommMonoid (val.Value base)] [SMul F (val.Value base)]
    (service : WeightedOracle.Layouts w (key.Value base) M F (val.Value base) C G)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * (WeightedRows.term service.evaluation).representation.encoding.words +
      service.signing.evaluated.representation.encoding.words < 2 ^ w)
    {generate : M → List (key.Value base × F)}
    (generator : Implementation .unit service.message
      (GeneratedWeighted.terms service.evaluation capacity countFits storageFits) generate)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {combine : F × (val.Value base × val.Value base) → val.Value base}
    (update : Implementation .unit service.evaluation.combine service.evaluation.cache.value combine)
    {updateSlots : Nat} (updateBuffers : update.program.code.memBound ≤ updateSlots) (updateReserve : updateSlots + 2 < 2 ^ w)
    (draw : Interactive.Code w)
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit service.responseInput service.point (respond signing))
    {responseSlots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ responseSlots)
    (responseReserve : responseSlots < 2 ^ w)
    (combineLaw : ∀ value, combine value = value.2.2 + value.1 • value.2.1)
    (zeroLaw : service.zero.val = 0)
    (source : ProbComp service.evaluation.cache.value.Value)
    (uniform : Subtype.val <$> source = ($ᵗ (val.Value base) : ProbComp (val.Value base)))

    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) .unit
      service.evaluation.cache.lookup.unit.representation service.evaluation.cache.value.representation (fun _ => source) draw)
    (domain : Nat → Request service randomBound × A → Prop)
    (advance : A × Reply service randomBound → B ⊕ (Request service randomBound × A))
    (advanceValid : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ represented original, WeightedCallerHandler.replyMatches service randomBound q represented original →
        HeadValid service randomBound domain remaining (advance (c, represented)))

include combineLaw zeroLaw uniform advanceValid in
theorem preserves (remaining : Nat) (value) (valid : Invariant service capacity randomBound domain (remaining + 1) value)
    (answer) (reached : answer ∈ support ((WeightedCallerHandler.denote service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source) (value.1.1, value.2))) :
    CallerControl.Valid (Invariant service capacity randomBound domain) remaining (advance (value.1.2, answer.1), answer.2) := by
  have ready := WeightedCallerHandler.ready_of_reserved service capacity countFits storageFits generator randomBound (value.1.1, value.2) valid.2
  obtain ⟨sourceAnswer, _, related⟩ := (WeightedCallerHandler.synchronizes service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response combineLaw zeroLaw source uniform (value.1.1, value.2) ready).left_support reached
  have localValid := advanceValid remaining value.1.1 value.1.2 valid.1 answer.1 sourceAnswer.1 related.1
  have reserved := (WeightedCallerHandler.step service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source (value.1.1, value.2) valid.2 answer reached).1
  cases head : advance (value.1.2, answer.1) with
  | inl result => trivial
  | inr pending => exact ⟨by simpa only [HeadValid, head] using localValid, reserved⟩

variable (state : Representation w A) (result : Representation w B)
    (fits : 8 * (1 + state.encoding.words + (request service randomBound randomFits).encoding.words +
      (reply service randomBound randomFits).encoding.words + result.encoding.words + service.store.representation.encoding.words) < 2 ^ w)

variable (continuation : Realizer .unit (CallerStep.resume (layout service randomBound randomFits state result fits))
      (CallerStep.next (layout service randomBound randomFits state result fits)) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → B ⊕ (Request service randomBound × A))
    (initialCode : Realizer .unit input (CallerStep.next (layout service randomBound randomFits state result fits)) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + service.store.representation.encoding.words < 2 ^ w)

def program (fuel : Nat) : Interactive.Code w :=
  CallerControl.program (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) advance continuation localNameFits (WeightedCallerHandler.code service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve) input initial initialCode initialNameFits inputFits fuel

variable (fuel : Nat) (admissible : U × service.store.Value → Prop)
    (initialValid : ∀ value, admissible value → HeadValid service randomBound domain fuel (initial value.1))
    (initialReserved : ∀ value, admissible value → WeightedOracle.Reserved service capacity fuel value.2.val)

omit [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
  [AddCommMonoid (val.Value base)] [SMul F (val.Value base)] in
include initialValid initialReserved in
theorem initial_invariant (value) (valid : admissible value) :
    CallerControl.Valid (Invariant service capacity randomBound domain) fuel (initial value.1, value.2) := by
  have localValid := initialValid value valid
  cases head : initial value.1 with
  | inl result => trivial
  | inr pending => exact ⟨by simpa only [HeadValid, head] using localValid, initialReserved value valid⟩

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved in
theorem refines : Interactive.RefinesOn admissible (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) .unit (input.prod service.store.representation inputFits)
    (CallerStep.output (layout service randomBound randomFits state result fits)) (fun value => CallerControl.start advance (WeightedCallerHandler.denote service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source) fuel (initial value.1, value.2))
    (program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel) :=
  CallerControl.program_refines (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) advance continuation localNameFits (Invariant service capacity randomBound domain)
    (ready service randomBound generate)
    (WeightedCallerHandler.refines service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect)
    (fun _ value valid => WeightedCallerHandler.ready_of_reserved service capacity countFits storageFits generator randomBound (value.1.1, value.2) valid.2)
    (preserves service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response combineLaw zeroLaw source uniform domain advance advanceValid)
    input initial initialCode initialNameFits inputFits fuel admissible
    (initial_invariant service capacity randomBound domain initial fuel admissible initialValid initialReserved)

end Signatures.Runtime.CaliperBackend.WeightedCaller
