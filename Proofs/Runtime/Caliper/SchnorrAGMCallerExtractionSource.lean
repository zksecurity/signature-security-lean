import Proofs.Runtime.Caliper.SchnorrAGMCallerExtraction
import Proofs.Runtime.Caliper.SchnorrAGMCallerFinishSource

/-! Exact original-machine semantics of the composed caller and terminal.
The proved caller invariant supplies canonical state and extraction room.
The source-machine query bound excludes cutoff; no completed reduction's
correctness or efficiency is assumed. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerExtraction
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G A U : Type} [Field F]
    (layout : Layouts w M F G qH qS randomBound A)
    [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq M] [DecidableEq G] [SampleableType F]
    (ops : Handler.Operations layout.service)
    (sub : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 - value.2))
    (divide : Implementation .unit layout.service.scheme.affine layout.service.scheme.scalar (fun value => value.1 / value.2))
    (subBuffers : sub.program.code.memBound ≤ ops.slots)
    (sampleSource : ProbComp layout.service.scheme.scalar.Value)
    (uniform : Subtype.val <$> sampleSource = ($ᵗ F : ProbComp F))

def finishSource (value : Option layout.forgery.Value × ((G × G) × Signatures.Runtime.SchnorrAGM.State F G M)) : ProbComp F :=
  match value.1 with
  | none => pure 0
  | some forgery => Prod.fst <$> (Signatures.Runtime.SchnorrAGM.finishScalar (Interface.decodeForgery forgery.val)).run value.2.2

include uniform in
theorem finish_source (value : layout.Packet) (ready : CallerFinish.ready layout.service.hash value)
    (reserved : CallerHandler.Reserved layout.service 0 0 value.2) :
    Subtype.val <$> CallerFinish.denote layout.service.hash ⟨0, ops.zeroValid⟩
      (extract layout ops sub divide subBuffers sampleSource) value =
      finishSource layout (CallerMachine.observe (CallerHandler.stored layout.service) value) := by
  rcases value with ⟨forgery | pending, saved⟩
  · exact CallerFinish.success_original layout.service.hash ops.zeroValid ops.mul ops.add sub divide
      ops.mulNames.buffers ops.addNames.buffers subBuffers ops.reserve sampleSource uniform (forgery, saved) ready
      (decodeState saved.val.2) (CallerHandler.Reserved.canonical layout.service reserved).symm
  · rfl

variable (domain : Nat → Nat → Nat → layout.Request × A → Prop)
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
    {V : Type} (machine : OracleMachine (Interface.sourceSpec F G M) V layout.forgery.Value)
    (stateView : layout.Request × A → machine.State) (inputView : U → V)
    (advanceMatches : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      ∀ next : (Interface.sourceSpec F G M).Range (CallerHandler.query layout.service q) → machine.State,
        machine.view (stateView (q, c)) = .inr ⟨CallerHandler.query layout.service q, next⟩ →
        ∀ represented original, CallerHandler.replyMatches layout.service q represented original →
          CallerMachine.Matches machine (CallerHandler.query layout.service) stateView (advance (c, represented)) (next original))
    (initialMatches : ∀ value, admissible value →
      CallerMachine.Matches machine (CallerHandler.query layout.service) stateView (initial value.1) (machine.init (inputView value.1)))

include uniform allowed advanceValid initialValid initialReserved advanceMatches initialMatches in
theorem called_source (sourceProgram : V → OracleComp (Interface.sourceSpec F G M) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (value : U × layout.service.scheme.store.Value) (valid : admissible value) :
    CallerMachine.observe (CallerHandler.stored layout.service) <$>
      called layout ops advance initial fuel sampleSource value =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ CallerHandler.original (sourceProgram (inputView value.1))).run (CallerHandler.stored layout.service value.2) := by
  apply CallerMachine.start_eq_simulateQ machine (CallerHandler.query layout.service) stateView
    (CallerHandler.stored layout.service) (CallerHandler.replyMatches layout.service) advance
    (CallerHandler.source layout.service ops sampleSource) CallerHandler.original (Caller.Invariant layout.service domain)
    _ _ (Caller.preserves layout.service ops sampleSource uniform domain allowed advance advanceValid)
    fuel (initial value.1, value.2) (inputView value.1)
    (Caller.initial_invariant layout.service domain initial fuel admissible initialValid initialReserved value valid)
    (initialMatches value valid) sourceProgram implements
  · intro remaining packet invariant
    obtain ⟨hashes, signatures, localValid, reserved⟩ := invariant
    exact CallerHandler.synchronizes_stored layout.service ops sampleSource uniform (packet.1.1, packet.2) reserved
      (allowed remaining hashes signatures _ _ localValid)
  · intro remaining q c saved invariant
    obtain ⟨hashes, signatures, localValid, _⟩ := invariant
    exact advanceMatches remaining hashes signatures q c localValid

include uniform allowed advanceValid initialValid initialReserved advanceMatches initialMatches in
theorem denote_source (sourceProgram : V → OracleComp (Interface.sourceSpec F G M) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (value : U × layout.service.scheme.store.Value) (valid : admissible value) :
    Subtype.val <$> denote layout ops sub divide subBuffers advance initial fuel sampleSource value =
      ((simulateQ CallerHandler.original (sourceProgram (inputView value.1))).run (CallerHandler.stored layout.service value.2) >>=
        fun answer => Prod.fst <$> (Signatures.Runtime.SchnorrAGM.finishScalar (Interface.decodeForgery answer.1.val)).run answer.2.2) := by
  have invoked := called_source layout ops sampleSource uniform domain allowed advance advanceValid initial fuel admissible
    initialValid initialReserved machine stateView inputView advanceMatches initialMatches sourceProgram implements value valid
  have finished : Subtype.val <$> denote layout ops sub divide subBuffers advance initial fuel sampleSource value =
      (called layout ops advance initial fuel sampleSource value >>=
        fun packet => finishSource layout (CallerMachine.observe (CallerHandler.stored layout.service) packet)) := by
    simp only [denote, map_bind]
    apply bind_congr_of_forall_mem_support
    intro packet reached
    have post := called_postcondition layout ops sampleSource uniform domain allowed advance advanceValid initial fuel admissible
      initialValid initialReserved value valid packet reached
    exact finish_source layout ops sub divide subBuffers sampleSource uniform packet (layout.packet_ready post packet.1) post.reserved
  rw [finished, ← bind_map_left, invoked, bind_map_left]
  rfl

variable (divBuffers : divide.program.code.memBound ≤ ops.slots) (sampler : Interactive.Code w)
    (sampleCorrect : Interactive.Refines layout.service.random.port .unit (PairSampling.input w).representation
      layout.service.scheme.scalar.representation (fun _ => sampleSource) sampler)
    (continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w) (input : Representation w U)
    (initialCode : Realizer .unit input (CallerStep.next layout.control) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.service.scheme.store.representation.encoding.words < 2 ^ w)

include uniform allowed advanceValid initialValid initialReserved advanceMatches initialMatches sampleCorrect in
theorem observe_source (sourceProgram : V → OracleComp (Interface.sourceSpec F G M) layout.forgery.Value)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (tape : RandomTape w) (value : U × layout.service.scheme.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod layout.service.scheme.store.representation inputFits).Holds value before) :
    (fun finished => Subtype.val <$> Interactive.observe layout.service.scheme.scalar.representation finished) <$>
      (program layout ops sub divide subBuffers divBuffers sampler advance continuation localNameFits input initial initialCode
        initialNameFits inputFits fuel).execute layout.service.random.port .unit tape before =
      some <$> ((simulateQ CallerHandler.original (sourceProgram (inputView value.1))).run (CallerHandler.stored layout.service value.2) >>=
        fun answer => Prod.fst <$> (Signatures.Runtime.SchnorrAGM.finishScalar (Interface.decodeForgery answer.1.val)).run answer.2.2) := by
  have observed := (refines layout ops sub divide subBuffers divBuffers sampleSource uniform domain allowed advance advanceValid
    initial fuel admissible initialValid initialReserved sampler sampleCorrect continuation localNameFits input initialCode initialNameFits inputFits).observe
      tape value valid before holds
  have equality := denote_source layout ops sub divide subBuffers sampleSource uniform domain allowed advance advanceValid initial fuel
    admissible initialValid initialReserved machine stateView inputView advanceMatches initialMatches sourceProgram implements value valid
  have mapped := congrArg (fun computation => (fun answer => Subtype.val <$> answer) <$> computation) observed
  rw [← equality]
  have middle : (fun answer => Subtype.val <$> answer) <$> some <$>
      denote layout ops sub divide subBuffers advance initial fuel sampleSource value =
      some <$> Subtype.val <$> denote layout ops sub divide subBuffers advance initial fuel sampleSource value :=
    (PFunctor.FreeM.comp_map _ _ _).symm.trans (PFunctor.FreeM.comp_map some Subtype.val _)
  exact (PFunctor.FreeM.comp_map _ _ _).trans (mapped.trans middle)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerExtraction
