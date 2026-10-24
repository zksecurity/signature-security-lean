import Proofs.Runtime.Caliper.SchnorrAGMCallerExtractionLayout

/-! The actual generated Schnorr caller followed by the constructed terminal.
Only local caller code and named arithmetic/sampling routines are supplied.
The caller postcondition establishes terminal admission at every supported exit. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerExtraction
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
variable {w qH qS randomBound : Nat} {M F G A U : Type} (layout : Layouts w M F G qH qS randomBound A)

section Program
variable [Zero F] [Mul F] [Add F] [Sub F] [Div F] [Neg F] [SMul F G] [Sub G]
    [DecidableEq F] [DecidableEq M] [DecidableEq G]
    (ops : Handler.Operations layout.service)
    (sub : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 / value.2))
    (subBuffers : sub.program.code.memBound ≤ ops.slots) (divBuffers : divide.program.code.memBound ≤ ops.slots)
    (sampler : Interactive.Code w)

def extractor : Interactive.Code w :=
  Extraction.code layout.service.hash ops.zeroValid ops.mul ops.add sub divide
    ops.mulNames.buffers ops.addNames.buffers subBuffers divBuffers ops.reserve layout.service.random.port sampler
def terminal : Interactive.Code w :=
  CallerFinish.code layout.service.hash layout.pending layout.exitFits ⟨0, ops.zeroValid⟩
    (extractor layout ops sub divide subBuffers divBuffers sampler)
def extract (sampleSource : ProbComp layout.service.scheme.scalar.Value) :=
  Extraction.source layout.service.hash ops.zeroValid ops.mul ops.add sub divide
    ops.mulNames.buffers ops.addNames.buffers subBuffers ops.reserve sampleSource

variable (advance : A × layout.Reply → layout.forgery.Value ⊕ (layout.Request × A))
    (continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U) (initial : U → layout.forgery.Value ⊕ (layout.Request × A))
    (initialCode : Realizer .unit input (CallerStep.next layout.control) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.service.scheme.store.representation.encoding.words < 2 ^ w)
    (fuel : Nat)

def caller : Interactive.Code w :=
  Caller.program layout.service ops sampler advance layout.state layout.forgery.representation layout.callerFits
    continuation localNameFits input initial initialCode initialNameFits inputFits fuel
def program : Interactive.Code w :=
  .seq (caller layout ops sampler advance continuation localNameFits input initial initialCode initialNameFits inputFits fuel)
    (terminal layout ops sub divide subBuffers divBuffers sampler)
def called (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (value : U × layout.service.scheme.store.Value) : ProbComp layout.Packet :=
  CallerControl.start advance (CallerHandler.source layout.service ops sampleSource) fuel (initial value.1, value.2)
def denote (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (value : U × layout.service.scheme.store.Value) : ProbComp layout.service.scheme.scalar.Value :=
  called layout ops advance initial fuel sampleSource value >>=
    CallerFinish.denote layout.service.hash ⟨0, ops.zeroValid⟩ (extract layout ops sub divide subBuffers sampleSource)
end Program

variable [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G] [SampleableType F]
    (ops : Handler.Operations layout.service)
    (sub : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 / value.2))
    (subBuffers : sub.program.code.memBound ≤ ops.slots) (divBuffers : divide.program.code.memBound ≤ ops.slots)
    (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))
    (domain : Nat → Nat → Nat → layout.Request × A → Prop)
    (allowed : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      CallerHandler.Allowed layout.service hashes signatures q)
    (advance : A × layout.Reply → layout.forgery.Value ⊕ (layout.Request × A))
    (advanceValid : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      ∀ represented original, CallerHandler.replyMatches layout.service q represented original →
        Caller.HeadValid layout.service domain remaining
          (hashes - CallerHandler.hashCharge layout.service q) (signatures - CallerHandler.signCharge layout.service q)
          (advance (c, represented)))
    (initial : U → layout.forgery.Value ⊕ (layout.Request × A))
    (fuel : Nat) (admissible : U × layout.service.scheme.store.Value → Prop)
    (initialValid : ∀ value, admissible value → Caller.HeadValid layout.service domain fuel qH qS (initial value.1))
    (initialReserved : ∀ value, admissible value → CallerHandler.Reserved layout.service qH qS value.2)

include uniform allowed advanceValid initialValid initialReserved in
theorem called_postcondition (value : U × layout.service.scheme.store.Value) (valid : admissible value)
    (answer : layout.Packet) (reached : answer ∈ support (called layout ops advance initial fuel sampleSource value)) :
    Caller.Postcondition layout.service value.2 answer.2 := by
  have invariant := Caller.initial_invariant layout.service domain initial fuel admissible initialValid initialReserved value valid
  have reserved := CallerHandler.Reserved.mono layout.service (initialReserved value valid) (Nat.zero_le _) (Nat.zero_le _)
  exact Caller.start_postcondition layout.service ops sampleSource uniform domain allowed advance advanceValid
    fuel (initial value.1, value.2) invariant reserved answer reached

include uniform allowed advanceValid initialValid initialReserved in
theorem called_ready (value : U × layout.service.scheme.store.Value) (valid : admissible value)
    (answer : layout.Packet) (reached : answer ∈ support (called layout ops advance initial fuel sampleSource value)) :
    CallerFinish.ready layout.service.hash answer :=
  layout.packet_ready (called_postcondition layout ops sampleSource uniform domain allowed advance advanceValid initial fuel
    admissible initialValid initialReserved value valid answer reached) answer.1

variable (sampler : Interactive.Code w)
    (sampleCorrect : Interactive.Refines layout.service.random.port .unit (PairSampling.input w).representation
      layout.service.scheme.scalar.representation (fun _ => sampleSource) sampler)
    (continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    (input : Representation w U)
    (initialCode : Realizer .unit input (CallerStep.next layout.control) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.service.scheme.store.representation.encoding.words < 2 ^ w)

include uniform allowed advanceValid initialValid initialReserved sampleCorrect in
theorem refines : Interactive.RefinesOn admissible layout.service.random.port .unit
    (input.prod layout.service.scheme.store.representation inputFits) layout.service.scheme.scalar.representation
    (denote layout ops sub divide subBuffers advance initial fuel sampleSource)
    (program layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel) := by
  have invoked := Caller.refines layout.service ops sampler sampleSource sampleCorrect uniform domain allowed advance advanceValid
    layout.state layout.forgery.representation layout.callerFits continuation localNameFits input initial initialCode initialNameFits
    inputFits fuel admissible initialValid initialReserved
  have extraction := Extraction.refines layout.service.hash ops.zeroValid ops.mul ops.add sub divide
    ops.mulNames.buffers ops.addNames.buffers subBuffers divBuffers ops.reserve layout.service.random.port sampleCorrect
  have finished := (CallerFinish.refines layout.service.hash layout.pending layout.exitFits layout.service.random.port
    extraction ⟨0, ops.zeroValid⟩).viewInput (CallerStep.output layout.control) id layout.packet_bytes
  exact invoked.seq finished (called_ready layout ops sampleSource uniform domain allowed advance advanceValid initial fuel
    admissible initialValid initialReserved)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerExtraction
