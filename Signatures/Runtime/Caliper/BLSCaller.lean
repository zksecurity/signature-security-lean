import Signatures.Runtime.Caliper.BLSCallerInvariant
import Signatures.Runtime.Caliper.CallerExecution

/-! Assemble a complete BLS caller from actual local initialization and
continuation code. The BLS handler, packet conversion and control flow are
constructed here; their correctness is not an input. Local caller invariants
need only be preserved for replies matching the pending typed source query. -/

namespace Signatures.Runtime.CaliperBackend.BLSCaller
open Caliper BoundedSource OracleComp OracleSpec BLSCallerPackets

section Layouts
variable {w : Nat} {M R C G A B : Type} (service : BLSReply.Layouts w M R C G)
    (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    (state : Representation w A) (result : Representation w B)
    (fits : 8 * (1 + state.encoding.words + (request service randomBound randomFits).encoding.words +
      (reply service randomBound randomFits).encoding.words + result.encoding.words + service.store.representation.encoding.words) < 2 ^ w)

def layout : CallerStep.Layouts w A (Request service randomBound) (Reply service randomBound) B service.store.Value :=
  ⟨state, request service randomBound randomFits, reply service randomBound randomFits,
    result, service.store.representation, fits, service.cache.wordFits⟩

def HeadValid (domain : Nat → Request service randomBound × A → Prop) (remaining : Nat)
    (head : B ⊕ (Request service randomBound × A)) : Prop :=
  match head with | .inl _ => True | .inr pending => domain remaining pending

def Invariant (domain : Nat → Request service randomBound × A → Prop) (remaining : Nat)
    (value : CallerControl.Frame A (Request service randomBound) service.store.Value) : Prop :=
  domain remaining value.1 ∧ BLSReply.Reserved service remaining value.2.val

end Layouts

variable {w : Nat} {C G A B U : Type} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] [SampleableType (val.Value base)]
    (service : BLSReply.Layouts w (key.Value base) (val.Value base) C G)
    (default : service.cache.value.Value) (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
    {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op) (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))
    {respond : Bool → val.Value base × C → G}
    (response : (signing : Bool) → Implementation .unit service.responseInput service.point (respond signing))
    {slots : Nat} (responseBuffers : ∀ signing, (response signing).program.code.memBound ≤ slots)
    (reserve : slots + 3 < 2 ^ w) (draw : Interactive.Code w)
    (drawSource : ProbComp service.cache.value.Value)
    (drawCorrect : Interactive.Refines (UniformQuery.port randomBound service.cache.wordFits randomFits) .unit
      service.cache.lookup.unit.representation service.cache.value.representation (fun _ => drawSource) draw)
    (drawLaw : Subtype.val <$> drawSource = ($ᵗ (val.Value base) : ProbComp (val.Value base)))
    (domain : Nat → Request service randomBound × A → Prop)
    (advance : A × Reply service randomBound → B ⊕ (Request service randomBound × A))
    (advanceValid : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ represented original, BLSCallerHandler.replyMatches service randomBound q represented original →
        HeadValid service randomBound domain remaining (advance (c, represented)))

include drawLaw advanceValid in
theorem preserves (remaining : Nat) (value) (valid : Invariant service randomBound domain (remaining + 1) value)
    (answer) (reached : answer ∈ support ((BLSCallerHandler.denote service default randomBound P comparison correct response responseBuffers reserve drawSource) (value.1.1, value.2))) :
    CallerControl.Valid (Invariant service randomBound domain) remaining (advance (value.1.2, answer.1), answer.2) := by
  have ready := BLSCallerHandler.ready_of_reserved service default randomBound (value.1.1, value.2) valid.2
  obtain ⟨source, _, related⟩ := (BLSCallerHandler.synchronizes service default randomBound P comparison correct response
    responseBuffers reserve drawSource drawLaw (value.1.1, value.2) ready).left_support reached
  have localValid := advanceValid remaining value.1.1 value.1.2 valid.1 answer.1 source.1 related.1
  have reserved := BLSCallerHandler.reserved_after service default randomBound P comparison correct response responseBuffers reserve
    drawSource drawLaw (value.1.1, value.2) valid.2 answer reached
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
  CallerControl.program (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.cache.wordFits randomFits) advance continuation localNameFits (BLSCallerHandler.code service default randomBound randomFits P comparison correct response responseBuffers reserve draw) input initial initialCode initialNameFits inputFits fuel

variable (fuel : Nat) (admissible : U × service.store.Value → Prop)
    (initialValid : ∀ value, admissible value → HeadValid service randomBound domain fuel (initial value.1))
    (initialReserved : ∀ value, admissible value → BLSReply.Reserved service fuel value.2.val)

omit [DecidableEq (key.Value base)] [SampleableType (val.Value base)] in
include initialValid initialReserved in
theorem initial_invariant (value) (valid : admissible value) :
    CallerControl.Valid (Invariant service randomBound domain) fuel (initial value.1, value.2) := by
  have localValid := initialValid value valid
  cases head : initial value.1 with
  | inl result => trivial
  | inr pending => exact ⟨by simpa only [HeadValid, head] using localValid, initialReserved value valid⟩

include drawCorrect drawLaw advanceValid initialValid initialReserved in
theorem refines : Interactive.RefinesOn admissible (UniformQuery.port randomBound service.cache.wordFits randomFits) .unit (input.prod service.store.representation inputFits)
    (CallerStep.output (layout service randomBound randomFits state result fits)) (fun value => CallerControl.start advance (BLSCallerHandler.denote service default randomBound P comparison correct response responseBuffers reserve drawSource) fuel (initial value.1, value.2))
    (program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel) :=
  CallerControl.program_refines (layout service randomBound randomFits state result fits) (UniformQuery.port randomBound service.cache.wordFits randomFits) advance continuation localNameFits (Invariant service randomBound domain)
    (ready service default randomBound)
    (BLSCallerHandler.refines service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawCorrect)
    (fun _ value valid => BLSCallerHandler.ready_of_reserved service default randomBound (value.1.1, value.2) valid.2)
    (preserves service default randomBound P comparison correct response responseBuffers reserve drawSource drawLaw domain advance advanceValid)
    input initial initialCode initialNameFits inputFits fuel admissible
    (initial_invariant service randomBound domain initial fuel admissible initialValid initialReserved)

end Signatures.Runtime.CaliperBackend.BLSCaller
