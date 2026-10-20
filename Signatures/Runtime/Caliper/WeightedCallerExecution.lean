import Signatures.Runtime.Caliper.WeightedCaller
import Signatures.Runtime.Caliper.WeightedCallerPostcondition

/-! The generated weighted caller executes the original source program. Only local
caller initialization/continuation correspondence and primitive sampling laws
are inputs. The complete weighted handler and its reservation invariant are derived. -/

namespace Signatures.Runtime.CaliperBackend.WeightedCaller
open Caliper BoundedSource OracleComp OracleSpec WeightedCallerPackets

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
    (initialReserved : ∀ value, admissible value → WeightedOracle.Reserved service capacity fuel value.2.val)

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved in
/-- The store-size postcondition holds of the bytes returned by the actual
caller execution, including early returns and cutoffs. It is derived from local
caller code and the constructed handler, not a completed-caller premise. -/
theorem execution_postcondition
    (tape : RandomTape w) (value : U × service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod service.store.representation inputFits).Holds value before)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
      state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).execute
        (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) .unit tape before)) :
    ∃ answer, (CallerStep.output (layout service randomBound randomFits state result fits)).Holds answer finished.state ∧
      Postcondition service capacity fuel value.2 answer.2 ∧
      WordIO.Exec .unit tape ((program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
        state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).lower
          (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits))
        before finished.state finished.trace finished.time finished.net finished.peak := by
  have refined := refines service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve combineLaw zeroLaw source uniform drawCorrect
    domain advance advanceValid state result fits continuation localNameFits input initial initialCode initialNameFits inputFits
    fuel admissible initialValid initialReserved
  obtain ⟨answer, supported, actual, equal, output, _, execution⟩ := (refined tape value valid before holds).right_support reached
  cases Option.some.inj equal
  exact ⟨answer, output, start_postcondition service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source
    advance fuel (initial value.1, value.2) (initialReserved value valid) answer supported, execution⟩

variable {V : Type}
    (machine : OracleMachine (Model.LazyAGM.advSpec (key.Value base) M G) V B)
    (stateView : Request service randomBound × A → machine.State) (inputView : U → V)
    (advanceMatches : ∀ remaining q c, domain (remaining + 1) (q, c) →
      ∀ next : (Model.LazyAGM.advSpec (key.Value base) M G).Range
          (WeightedCallerHandler.query service randomBound q) → machine.State,
        machine.view (stateView (q, c)) = .inr ⟨WeightedCallerHandler.query service randomBound q, next⟩ →
        ∀ represented original, WeightedCallerHandler.replyMatches service randomBound q represented original →
          CallerMachine.Matches machine (WeightedCallerHandler.query service randomBound) stateView
            (advance (c, represented)) (next original))
    (initialMatches : ∀ value, admissible value →
      CallerMachine.Matches machine (WeightedCallerHandler.query service randomBound) stateView
        (initial value.1) (machine.init (inputView value.1)))

include drawCorrect combineLaw zeroLaw uniform advanceValid initialValid initialReserved advanceMatches initialMatches in
/-- Equality of free probabilistic trees, retaining the final private store.
The original machine's implementation certificate excludes the fuel cutoff. -/
theorem observe_source
    (sourceProgram : V → OracleComp (Model.LazyAGM.advSpec (key.Value base) M G) B)
    (implements : machine.ImplementsWithin sourceProgram fuel)
    (tape : RandomTape w) (value : U × service.store.Value) (valid : admissible value)
    (before : State w) (holds : (input.prod service.store.representation inputFits).Holds value before) :
    (fun finished => CallerMachine.observe Subtype.val <$>
      Interactive.observe (CallerStep.output (layout service randomBound randomFits state result fits)) finished) <$>
      (program service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve advance
        state result fits continuation localNameFits input initial initialCode initialNameFits inputFits fuel).execute
          (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) .unit tape before =
      (fun finished => some (some finished.1, finished.2)) <$>
        (simulateQ (WeightedCallerHandler.original generate respond) (sourceProgram (inputView value.1))).run value.2.val := by
  exact CallerMachine.program_observe_source machine (WeightedCallerHandler.query service randomBound) stateView
    Subtype.val (WeightedCallerHandler.replyMatches service randomBound) advance
    (WeightedCallerHandler.denote service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response source)
    (WeightedCallerHandler.original generate respond) (Invariant service capacity randomBound domain)
    (fun _ packet valid => WeightedCallerHandler.synchronizes service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response combineLaw zeroLaw source uniform (packet.1.1, packet.2)
        (WeightedCallerHandler.ready_of_reserved service capacity countFits storageFits generator randomBound (packet.1.1, packet.2) valid.2))
    (fun remaining q c _ valid => advanceMatches remaining q c valid.1)
    (preserves service capacity countFits storageFits generator randomBound P comparison correct update updateBuffers updateReserve response combineLaw zeroLaw source uniform domain advance advanceValid)
    (layout service randomBound randomFits state result fits)
    (UniformQuery.port randomBound service.evaluation.cache.wordFits randomFits) continuation localNameFits
    (WeightedCallerHandler.code service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve)
    (ready service randomBound generate)
    (WeightedCallerHandler.refines service capacity countFits storageFits generator randomBound randomFits P comparison correct update updateBuffers updateReserve draw response responseBuffers responseReserve drawCorrect)
    (fun _ packet valid => WeightedCallerHandler.ready_of_reserved service capacity countFits storageFits generator randomBound (packet.1.1, packet.2) valid.2)
    input initial initialCode initialNameFits inputFits fuel admissible
    (initial_invariant service capacity randomBound domain initial fuel admissible initialValid initialReserved)
    inputView initialMatches sourceProgram implements tape value valid before holds

end Signatures.Runtime.CaliperBackend.WeightedCaller
