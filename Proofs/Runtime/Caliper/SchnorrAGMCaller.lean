import Proofs.Runtime.Caliper.SchnorrAGMCallerInvariant
import Proofs.Runtime.Caliper.CallerExecution

/-! Generated Schnorr caller control from actual local initialization and
continuation routines. Separate hash/sign allowances are proof invariants;
the handler and its private-store reservation are constructed here. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Caller
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
variable {w qH qS randomBound : Nat} {M F G A B U : Type}
    (service : Handler.Layouts w M F G qH qS randomBound)

def layout (state : Representation w A) (result : Representation w B)
    (fits : 8 * (1 + state.encoding.words + (request service).encoding.words + (reply service).encoding.words +
      result.encoding.words + service.scheme.store.representation.encoding.words) < 2 ^ w) :
    CallerStep.Layouts w A (Request service) (Reply service) B service.scheme.store.Value :=
  ⟨state, request service, reply service, result, service.scheme.store.representation, fits, service.scheme.wordFits⟩

def HeadValid (domain : Nat → Nat → Nat → Request service × A → Prop) (remaining hashes signatures : Nat)
    (head : B ⊕ (Request service × A)) : Prop :=
  match head with | .inl _ => True | .inr pending => domain remaining hashes signatures pending

section Program
variable [Zero F] [Mul F] [Add F] [Neg F] [SMul F G] [Sub G]
    [DecidableEq F] [DecidableEq M] [DecidableEq G] (ops : Handler.Operations service) (sampler : Interactive.Code w)
    (advance : A × Reply service → B ⊕ (Request service × A))
    (state : Representation w A) (result : Representation w B)
    (fits : 8 * (1 + state.encoding.words + (request service).encoding.words + (reply service).encoding.words +
      result.encoding.words + service.scheme.store.representation.encoding.words) < 2 ^ w)
    (continuation : Realizer .unit (CallerStep.resume (layout service state result fits))
      (CallerStep.next (layout service state result fits)) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → B ⊕ (Request service × A))
    (initialCode : Realizer .unit input (CallerStep.next (layout service state result fits)) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + service.scheme.store.representation.encoding.words < 2 ^ w)

def program (fuel : Nat) : Interactive.Code w :=
  CallerControl.program (layout service state result fits) service.random.port advance continuation localNameFits
    (CallerHandler.code service ops sampler) input initial initialCode initialNameFits inputFits fuel
end Program

variable [Field F]
def Invariant (domain : Nat → Nat → Nat → Request service × A → Prop) (remaining : Nat)
    (value : CallerControl.Frame A (Request service) service.scheme.store.Value) : Prop :=
  ∃ hashes signatures, domain remaining hashes signatures value.1 ∧ CallerHandler.Reserved service hashes signatures value.2

variable [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G] [SampleableType F]
    (ops : Handler.Operations service) (sampler : Interactive.Code w) (sampleSource : ProbComp service.scheme.scalar.Value)
    (sampleCorrect : Interactive.Refines service.random.port .unit (PairSampling.input w).representation service.scheme.scalar.representation
      (fun _ => sampleSource) sampler)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))
    (domain : Nat → Nat → Nat → Request service × A → Prop)
    (allowed : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      CallerHandler.Allowed service hashes signatures q)
    (advance : A × Reply service → B ⊕ (Request service × A))
    (advanceValid : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      ∀ represented original, CallerHandler.replyMatches service q represented original →
        HeadValid service domain remaining (hashes - CallerHandler.hashCharge service q) (signatures - CallerHandler.signCharge service q)
          (advance (c, represented)))

omit [AddCommGroup G] [Module F G] [DecidableEq F] [SampleableType F] in
include allowed in
theorem available (remaining : Nat) (value) (valid : Invariant service domain (remaining + 1) value) :
    ready service (value.1.1, value.2) := by
  obtain ⟨hashes, signatures, localValid, reserved⟩ := valid
  exact CallerHandler.ready_of_reserved service (value.1.1, value.2) reserved
    (allowed remaining hashes signatures _ _ localValid)

include uniform allowed advanceValid in
theorem preserves (remaining : Nat) (value) (valid : Invariant service domain (remaining + 1) value)
    (answer) (reached : answer ∈ support (CallerHandler.source service ops sampleSource (value.1.1, value.2))) :
    CallerControl.Valid (Invariant service domain) remaining (advance (value.1.2, answer.1), answer.2) := by
  obtain ⟨hashes, signatures, localValid, reserved⟩ := valid
  have allowedQuery := allowed remaining hashes signatures _ _ localValid
  obtain ⟨original, _, related⟩ := (CallerHandler.synchronizes_stored service ops sampleSource uniform
    (value.1.1, value.2) reserved allowedQuery).left_support reached
  have localNext := advanceValid remaining hashes signatures _ _ localValid answer.1 original.1 related.1
  have next := CallerHandler.reserved_after service ops sampleSource uniform (value.1.1, value.2) reserved allowedQuery answer reached
  cases head : advance (value.1.2, answer.1) with
  | inl result => trivial
  | inr pending => exact ⟨_, _, by simpa only [HeadValid, head] using localNext, next⟩

variable (state : Representation w A) (result : Representation w B)
    (fits : 8 * (1 + state.encoding.words + (request service).encoding.words + (reply service).encoding.words +
      result.encoding.words + service.scheme.store.representation.encoding.words) < 2 ^ w)
    (continuation : Realizer .unit (CallerStep.resume (layout service state result fits))
      (CallerStep.next (layout service state result fits)) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → B ⊕ (Request service × A))
    (initialCode : Realizer .unit input (CallerStep.next (layout service state result fits)) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + service.scheme.store.representation.encoding.words < 2 ^ w)
    (fuel : Nat) (admissible : U × service.scheme.store.Value → Prop)
    (initialValid : ∀ value, admissible value → HeadValid service domain fuel qH qS (initial value.1))
    (initialReserved : ∀ value, admissible value → CallerHandler.Reserved service qH qS value.2)

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G] [SampleableType F] in
include initialValid initialReserved in
theorem initial_invariant (value) (valid : admissible value) :
    CallerControl.Valid (Invariant service domain) fuel (initial value.1, value.2) := by
  have localValid := initialValid value valid
  cases head : initial value.1 with
  | inl result => trivial
  | inr pending => exact ⟨qH, qS, by simpa only [HeadValid, head] using localValid, initialReserved value valid⟩

include sampleCorrect uniform allowed advanceValid initialValid initialReserved in
theorem refines : Interactive.RefinesOn admissible service.random.port .unit
    (input.prod service.scheme.store.representation inputFits) (CallerStep.output (layout service state result fits))
    (fun value => CallerControl.start advance (CallerHandler.source service ops sampleSource) fuel (initial value.1, value.2))
    (program service ops sampler advance state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel) :=
  CallerControl.program_refines (layout service state result fits) service.random.port advance continuation localNameFits
    (Invariant service domain) (ready service) (CallerHandler.refines service ops sampleCorrect)
    (available service domain allowed)
    (preserves service ops sampleSource uniform domain allowed advance advanceValid)
    input initial initialCode initialNameFits inputFits fuel admissible
    (initial_invariant service domain initial fuel admissible initialValid initialReserved)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Caller
