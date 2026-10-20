import Signatures.Runtime.Caliper.SchnorrAGMCallerPostcondition

/-! Actual caller execution preserves extraction room and agrees with the
original oracle machine. Only local caller code/correspondence and primitive
implementations remain parameters; the handler and capacity proof are derived. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Caller
open Caliper BoundedSource OracleComp OracleSpec CallerPackets
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS randomBound : Nat} {M F G A B U : Type} [Field F]
    (service : Handler.Layouts w M F G qH qS randomBound)
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

include sampleCorrect uniform allowed advanceValid initialValid initialReserved in
theorem execution_postcondition
    (tape : RandomTape w) (value : U × service.scheme.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod service.scheme.store.representation inputFits).Holds value before)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program service ops sampler advance state result fits continuation localNameFits
      input initial initialCode initialNameFits inputFits fuel).execute service.random.port .unit tape before)) :
    ∃ answer, (CallerStep.output (layout service state result fits)).Holds answer finished.state ∧
      Postcondition service value.2 answer.2 ∧
      WordIO.Exec .unit tape ((program service ops sampler advance state result fits continuation localNameFits
        input initial initialCode initialNameFits inputFits fuel).lower service.random.port)
        before finished.state finished.trace finished.time finished.net finished.peak := by
  have refined := refines service ops sampler sampleSource sampleCorrect uniform domain allowed advance advanceValid state result fits
    continuation localNameFits input initial initialCode initialNameFits inputFits fuel admissible initialValid initialReserved
  obtain ⟨answer, supported, actual, equal, output, _, execution⟩ := (refined tape value valid before holds).right_support reached
  cases Option.some.inj equal
  exact ⟨answer, output, start_postcondition service ops sampleSource uniform domain allowed advance advanceValid fuel
    (initial value.1, value.2) (initial_invariant service domain initial fuel admissible initialValid initialReserved value valid)
    (CallerHandler.Reserved.mono service (initialReserved value valid) (Nat.zero_le _) (Nat.zero_le _)) answer supported, execution⟩

variable {V : Type} (machine : OracleMachine (Interface.sourceSpec F G M) V B)
    (stateView : Request service × A → machine.State) (inputView : U → V)
    (advanceMatches : ∀ remaining hashes signatures q c, domain (remaining + 1) hashes signatures (q, c) →
      ∀ next : (Interface.sourceSpec F G M).Range (CallerHandler.query service q) → machine.State,
        machine.view (stateView (q, c)) = .inr ⟨CallerHandler.query service q, next⟩ →
        ∀ represented original, CallerHandler.replyMatches service q represented original →
          CallerMachine.Matches machine (CallerHandler.query service) stateView (advance (c, represented)) (next original))
    (initialMatches : ∀ value, admissible value →
      CallerMachine.Matches machine (CallerHandler.query service) stateView (initial value.1) (machine.init (inputView value.1)))

include sampleCorrect uniform allowed advanceValid initialValid initialReserved advanceMatches initialMatches in
theorem observe_source (sourceProgram : V → OracleComp (Interface.sourceSpec F G M) B)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (tape : RandomTape w) (value : U × service.scheme.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod service.scheme.store.representation inputFits).Holds value before) :
    (fun finished => CallerMachine.observe (CallerHandler.stored service) <$>
      Interactive.observe (CallerStep.output (layout service state result fits)) finished) <$>
        (program service ops sampler advance state result fits continuation localNameFits
          input initial initialCode initialNameFits inputFits fuel).execute service.random.port .unit tape before =
      (fun finished => some (some finished.1, finished.2)) <$>
        (simulateQ CallerHandler.original (sourceProgram (inputView value.1))).run (CallerHandler.stored service value.2) := by
  apply CallerMachine.program_observe_source machine (CallerHandler.query service) stateView
    (CallerHandler.stored service) (CallerHandler.replyMatches service) advance (CallerHandler.source service ops sampleSource)
    CallerHandler.original (Invariant service domain) _ _
    (preserves service ops sampleSource uniform domain allowed advance advanceValid)
    (layout service state result fits) service.random.port continuation localNameFits (CallerHandler.code service ops sampler)
    (ready service) (CallerHandler.refines service ops sampleCorrect) (available service domain allowed)
    input initial initialCode initialNameFits inputFits fuel admissible
    (initial_invariant service domain initial fuel admissible initialValid initialReserved)
    inputView initialMatches sourceProgram implements tape value valid before holds
  · intro remaining packet invariant
    obtain ⟨hashes, signatures, localValid, reserved⟩ := invariant
    exact CallerHandler.synchronizes_stored service ops sampleSource uniform (packet.1.1, packet.2) reserved
      (allowed remaining hashes signatures _ _ localValid)
  · intro remaining q c saved invariant
    obtain ⟨hashes, signatures, localValid, _⟩ := invariant
    exact advanceMatches remaining hashes signatures q c localValid

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Caller
