import Signatures.Runtime.Caliper.CallerMachine
import Signatures.Runtime.Caliper.CallerControlStorage

/-! Complete caller endpoints: observation of actual word execution agrees with
the original machine, and time/code/name/initial-capacity accounts bound every
visited state of that same execution. Source correspondence and primitive
implementation obligations remain explicit. -/

namespace Signatures.Runtime.CaliperBackend
open Caliper OracleComp OracleSpec

namespace CallerControl
variable {w : Nat} {C Q R B S A I : Type} {spec : OracleSpec I}
    (layout : CallerStep.Layouts w C Q R B S) (port : Interactive.Port w spec)
    (advance : C × R → B ⊕ (Q × C))
    (continuation : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w)
    {handler : Interactive.Code w} {H : Q × S → OracleComp spec (R × S)}
    (invariant : Nat → Frame C Q S → Prop) (ready : Q × S → Prop)
    (handlerRefines : Interactive.RefinesOn ready port .unit (CallerStep.request layout) (CallerStep.reply layout) H handler)
    (available : ∀ remaining value, invariant (remaining + 1) value → ready (value.1.1, value.2))
    (preserves : ∀ remaining value, invariant (remaining + 1) value →
      ∀ reply ∈ support (H (value.1.1, value.2)), Valid invariant remaining (advance (value.1.2, reply.1), reply.2))
    (input : Representation w A) (initial : A → B ⊕ (Q × C))
    (initialCode : Realizer .unit input (CallerStep.next layout) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.store.encoding.words < 2 ^ w)
    (fuel : Nat) (admissible : A × S → Prop)
    (initialValid : ∀ value, admissible value → Valid invariant fuel (initial value.1, value.2))

def timeBudget (inputWords width handlerTime localTime initialTime fuel : Nat) : Nat :=
  initialTime + 8 * inputWords + 88 * width + 4 + fuel * (handlerTime + localTime + 172 * width + 6)

include handlerRefines available preserves initialValid in
theorem program_resources (handlerTime localTime initialTime : Nat)
    (handlerBound : Interactive.TimeBoundOn ready port .unit (CallerStep.request layout) handler handlerTime)
    (localBound : ∀ value, continuation.time value ≤ localTime)
    (initialBound : ∀ value, initialCode.time value ≤ initialTime)
    (slots : Nat) (room : 3 ≤ slots) (handlerNames : WordIO.NamesAccounted (handler.lower port) slots)
    (localNames : NamesAccounted continuation.code slots) (initialNames : NamesAccounted initialCode.code slots)
    (tape : RandomTape w) (value : A × S) (valid : admissible value) (before : State w)
    (holds : (input.prod layout.store inputFits).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w)
    (reached : some finished ∈ support ((program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel).execute port .unit tape before)) :
    let code := program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel
    let words := programWords layout port advance continuation handler input initial initialCode fuel
    let time := timeBudget input.encoding.words (CallerStep.width layout) handlerTime localTime initialTime fuel
    finished.time ≤ time ∧ ∃ answer ∈ support (start advance H fuel (initial value.1, value.2)),
      (CallerStep.output layout).Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower port).memBound) ∧ between.WellFormed ∧
          ((code.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower port).memBound) ≤
            words + 4 * (slots + words) + registers + 3 * buffers + before.liveMem buffers + time := by
  have refined := program_refines layout port advance continuation localNameFits invariant ready handlerRefines available preserves
    input initial initialCode initialNameFits inputFits fuel admissible initialValid
  have bounded := program_time layout port advance continuation localNameFits invariant ready handlerRefines available handlerBound localBound preserves
    input initial initialCode initialNameFits inputFits fuel admissible initialValid initialTime initialBound
  have stored := program_words layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel
  have named := program_names layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits
    room handlerNames localNames initialNames fuel
  exact refined.resources bounded stored
    ⟨named.registers.trans (Nat.add_le_add_left stored slots), named.buffers.trans (Nat.add_le_add_left stored slots)⟩
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
end CallerControl

namespace CallerMachine
open CallerControl

variable {w : Nat} {C Q R B S A U T I J : Type} {source : OracleSpec I} {target : OracleSpec J}
    (machine : OracleMachine source A B) (query : Q → I) (state : C → machine.State)
    (stored : S → T) (replyMatches : (q : Q) → R → source.Range (query q) → Prop)
    (advance : C × R → B ⊕ (Q × C)) (H : Q × S → OracleComp target (R × S))
    (original : QueryImpl source (StateT T (OracleComp target))) (invariant : Nat → Frame C Q S → Prop)
    (handlerMatches : ∀ remaining value, invariant (remaining + 1) value →
      Synchronizes (replyRelation query stored replyMatches value.1.1)
        (H (value.1.1, value.2)) ((original (query value.1.1)).run (stored value.2)))
    (advanceMatches : ∀ remaining q c saved, invariant (remaining + 1) ((q, c), saved) →
      ∀ next : source.Range (query q) → machine.State,
        machine.view (state c) = .inr ⟨query q, next⟩ →
        ∀ reply originalReply, replyMatches q reply originalReply →
          Matches machine query state (advance (c, reply)) (next originalReply))
    (preserves : ∀ remaining value, invariant (remaining + 1) value →
      ∀ reply ∈ support (H (value.1.1, value.2)), Valid invariant remaining (advance (value.1.2, reply.1), reply.2))
    (layout : CallerStep.Layouts w C Q R B S) (port : Interactive.Port w target)
    (continuation : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) advance)
    (localNameFits : continuation.savedBuffer < 2 ^ w) (handler : Interactive.Code w)
    (ready : Q × S → Prop)
    (handlerRefines : Interactive.RefinesOn ready port .unit (CallerStep.request layout) (CallerStep.reply layout) H handler)
    (available : ∀ remaining value, invariant (remaining + 1) value → ready (value.1.1, value.2))
    (input : Representation w U) (initial : U → B ⊕ (Q × C))
    (initialCode : Realizer .unit input (CallerStep.next layout) initial)
    (initialNameFits : initialCode.savedBuffer < 2 ^ w)
    (inputFits : input.encoding.words + layout.store.encoding.words < 2 ^ w)

include handlerMatches advanceMatches preserves handlerRefines available in
theorem program_observe (fuel : Nat) (admissible : U × S → Prop)
    (initialValid : ∀ value, admissible value → Valid invariant fuel (initial value.1, value.2))
    (inputView : U → A)
    (initialMatches : ∀ value, admissible value → Matches machine query state (initial value.1) (machine.init (inputView value.1)))
    (tape : RandomTape w) (value : U × S) (valid : admissible value) (before : State w)
    (holds : (input.prod layout.store inputFits).Holds value before) :
    (fun result => observe stored <$> Interactive.observe (CallerStep.output layout) result) <$>
      (program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel).execute port .unit tape before =
      some <$> (machine.runWithInput original fuel (inputView value.1)).run (stored value.2) := by
  have compiled := program_refines layout port advance continuation localNameFits invariant ready handlerRefines available preserves
    input initial initialCode initialNameFits inputFits fuel admissible initialValid
  have output := (compiled tape value valid before holds).map_eq
    (fun packet => some (observe stored packet))
    (fun result => observe stored <$> Interactive.observe (CallerStep.output layout) result)
    (by intro packet result related; rw [related.observe]; rfl)
  have sourceEq := start_eq_runWith machine query state stored replyMatches advance H original invariant
    handlerMatches advanceMatches preserves fuel (initial value.1, value.2) (machine.init (inputView value.1))
      (initialValid value valid) (initialMatches value valid)
  apply output.symm.trans
  unfold PFunctor.DynSystem.DynComputation.runWithInput
  simpa only [Functor.map_map, Function.comp_def] using congrArg (fun computation => some <$> computation) sourceEq

include handlerMatches advanceMatches preserves handlerRefines available in
/-- With the original machine's implementation certificate, actual controller
execution observes the source program and its final private store, with no fuel
cutoff. The outer option is the word-execution observation, the inner option is
the source machine's return/cutoff observation. -/
theorem program_observe_source (fuel : Nat) (admissible : U × S → Prop)
    (initialValid : ∀ value, admissible value → Valid invariant fuel (initial value.1, value.2))
    (inputView : U → A)
    (initialMatches : ∀ value, admissible value → Matches machine query state (initial value.1) (machine.init (inputView value.1)))
    (sourceProgram : A → OracleComp source B) (implements : machine.ImplementsWithin sourceProgram fuel)
    (tape : RandomTape w) (value : U × S) (valid : admissible value) (before : State w)
    (holds : (input.prod layout.store inputFits).Holds value before) :
    (fun result => observe stored <$> Interactive.observe (CallerStep.output layout) result) <$>
      (program layout port advance continuation localNameFits handler input initial initialCode initialNameFits inputFits fuel).execute port .unit tape before =
      (fun result => some (some result.1, result.2)) <$>
        (simulateQ original (sourceProgram (inputView value.1))).run (stored value.2) := by
  have observed := program_observe machine query state stored replyMatches advance H original invariant
    handlerMatches advanceMatches preserves layout port continuation localNameFits handler ready handlerRefines available
    input initial initialCode initialNameFits inputFits fuel admissible initialValid inputView initialMatches tape value valid before holds
  rw [implements.simulateQ_run_eq original (inputView value.1), StateT.run_map, Functor.map_map] at observed
  exact observed

end CallerMachine
end Signatures.Runtime.CaliperBackend
