import Proofs.Runtime.Caliper.BLSCaller
import Proofs.Runtime.Caliper.BLSCallerPostcondition

/-! The generated BLS caller executes the original source program. Only local
caller initialization/continuation correspondence and primitive sampling laws
are inputs. The complete BLS handler and its reservation invariant are derived. -/

namespace Signatures.Runtime.CaliperBackend.BLSCaller
open Caliper BoundedSource OracleComp OracleSpec BLSCallerPackets

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

variable (fuel : Nat) (admissible : U × service.store.Value → Prop)
    (initialValid : ∀ value, admissible value → HeadValid service randomBound domain fuel (initial value.1))
    (initialReserved : ∀ value, admissible value → BLSReply.Reserved service fuel value.2.val)

include drawCorrect drawLaw advanceValid initialValid initialReserved in
/-- The store-size postcondition holds of the bytes returned by the actual
caller execution, including early returns and cutoffs. It is derived from local
caller code and the constructed handler, not a completed-caller premise. -/
theorem execution_postcondition
    (tape : RandomTape w) (value : U × service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod service.store.representation inputFits).Holds value before)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).execute
        (UniformQuery.port randomBound service.cache.wordFits randomFits) .unit tape before)) :
    ∃ answer, (CallerStep.output (layout service randomBound randomFits state result fits)).Holds answer finished.state ∧
      Postcondition service fuel value.2 answer.2 ∧
      WordIO.Exec .unit tape ((program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
        state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).lower
          (UniformQuery.port randomBound service.cache.wordFits randomFits))
        before finished.state finished.trace finished.time finished.net finished.peak := by
  have refined := refines service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawSource drawCorrect drawLaw
    domain advance advanceValid state result fits continuation localNameFits input initial initialCode initialNameFits inputFits
    fuel admissible initialValid initialReserved
  obtain ⟨answer, supported, actual, equal, output, _, execution⟩ := (refined tape value valid before holds).right_support reached
  cases Option.some.inj equal
  exact ⟨answer, output, start_postcondition service default randomBound P comparison correct response responseBuffers reserve drawSource drawLaw
    advance fuel (initial value.1, value.2) (initialReserved value valid) answer supported, execution⟩

variable {V : Type}
    (machine : OracleMachine (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G) V B)
    (stateView : Request service randomBound × A → machine.State) (inputView : U → V)
    (advanceMatches : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ next : (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G).Range
          (BLSCallerHandler.query service randomBound q) → machine.State,
        machine.view (stateView (q, c)) = .inr ⟨BLSCallerHandler.query service randomBound q, next⟩ →
        ∀ represented original, BLSCallerHandler.replyMatches service randomBound q represented original →
          CallerMachine.Matches machine (BLSCallerHandler.query service randomBound) stateView
            (advance (c, represented)) (next original))
    (initialMatches : ∀ value, admissible value →
      CallerMachine.Matches machine (BLSCallerHandler.query service randomBound) stateView
        (initial value.1) (machine.init (inputView value.1)))

include drawCorrect drawLaw advanceValid initialValid initialReserved advanceMatches initialMatches in
/-- Equality of free probabilistic trees, retaining the final private store.
The original machine's implementation certificate excludes the fuel cutoff. -/
theorem observe_source
    (sourceProgram : V → OracleComp (Model.LazyAGM.advSpec (key.Value base) (key.Value base) G) B)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (tape : RandomTape w) (value : U × service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod service.store.representation inputFits).Holds value before) :
    (fun finished => CallerMachine.observe Subtype.val <$>
      Interactive.observe (CallerStep.output (layout service randomBound randomFits state result fits)) finished) <$>
      (program service default randomBound randomFits P comparison correct response responseBuffers reserve draw advance
        state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).execute
          (UniformQuery.port randomBound service.cache.wordFits randomFits) .unit tape before =
      (fun finished => some (some finished.1, finished.2)) <$>
        (simulateQ (BLSCallerHandler.original respond) (sourceProgram (inputView value.1))).run value.2.val := by
  exact CallerMachine.program_observe_source machine (BLSCallerHandler.query service randomBound) stateView
    Subtype.val (BLSCallerHandler.replyMatches service randomBound) advance
    (BLSCallerHandler.denote service default randomBound P comparison correct response responseBuffers reserve drawSource)
    (BLSCallerHandler.original respond) (Invariant service randomBound domain)
    (fun _ packet valid => BLSCallerHandler.synchronizes service default randomBound P comparison correct response
      responseBuffers reserve drawSource drawLaw (packet.1.1, packet.2)
        (BLSCallerHandler.ready_of_reserved service default randomBound (packet.1.1, packet.2) valid.2))
    (fun remaining q c _ valid => advanceMatches remaining q c valid.1)
    (preserves service default randomBound P comparison correct response responseBuffers reserve drawSource drawLaw domain advance advanceValid)
    (layout service randomBound randomFits state result fits)
    (UniformQuery.port randomBound service.cache.wordFits randomFits) continuation localNameFits
    (BLSCallerHandler.code service default randomBound randomFits P comparison correct response responseBuffers reserve draw)
    (ready service default randomBound)
    (BLSCallerHandler.refines service default randomBound randomFits P comparison correct response responseBuffers reserve draw drawCorrect)
    (fun _ packet valid => BLSCallerHandler.ready_of_reserved service default randomBound (packet.1.1, packet.2) valid.2)
    input initial initialCode initialNameFits inputFits fuel admissible
    (initial_invariant service randomBound domain initial fuel admissible initialValid initialReserved)
    inputView initialMatches sourceProgram implements tape value valid before holds

end Signatures.Runtime.CaliperBackend.BLSCaller
