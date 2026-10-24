import Proofs.Runtime.Caliper.CallerExecution
import Proofs.Runtime.Caliper.UniformQuery
import Proofs.Runtime.Caliper.Words
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend
open PFunctor.DynSystem.DynComputation

namespace SignaturesTest.CaliperCallerControl

private def word := wordRepresentation 10 (by decide)
private def port := UniformQuery.port (w := 10) 3 (by decide) (by decide)
private def layout : CallerStep.Layouts 10 (Word 10) (Fin 4) (UniformQuery.Reply 3) (Word 10) (Word 10) :=
  ⟨word, port.request, port.reply, word, word, by decide, by decide⟩
private def initialCode := Realizer.identity (cost := CostModel.unit) (by decide) (CallerStep.next layout)
private def advance (value : Word 10 × UniformQuery.Reply 3) : Word 10 ⊕ (Fin 4 × Word 10) := .inl value.1
private def continuation : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) advance :=
  ((firstRealizer .unit (by decide) word port.reply (by decide) (by decide)).then
    (inlRealizer .unit (by decide) word (CallerStep.pending layout) (by decide) (by decide))).viewOutput
      (CallerStep.next layout) advance (fun _ => rfl)
private def handler := UniformQuery.forward 3 (by decide) (by decide) word
private def handlerSource := UniformQuery.forwardSource (S := Word 10) 3
private def ready (_ : Fin 4 × Word 10) := True
private def invariant (_ : Nat) (value : CallerControl.Frame (Word 10) (Fin 4) (Word 10)) := value.1.2.toNat = value.1.1.val
private def admissible := CallerControl.Valid (B := Word 10) invariant 1
private def controller (fuel : Nat) := CallerControl.program layout port advance continuation (by decide) handler
  (CallerStep.next layout) id initialCode (by decide) (by decide) fuel

private theorem handler_refines : Interactive.RefinesOn ready port .unit (CallerStep.request layout) (CallerStep.reply layout) handlerSource handler :=
  (UniformQuery.forward_refines 3 (by decide) (by decide) word (by decide)).on ready
private theorem available (remaining : Nat) (value : CallerControl.Frame (Word 10) (Fin 4) (Word 10))
    (_ : invariant (remaining + 1) value) : ready (value.1.1, value.2) := trivial
private theorem preserves (remaining : Nat) (value : CallerControl.Frame (Word 10) (Fin 4) (Word 10))
    (_ : invariant (remaining + 1) value) (reply) (_ : reply ∈ support (handlerSource (value.1.1, value.2))) :
    CallerControl.Valid invariant remaining (advance (value.1.2, reply.1), reply.2) := trivial
private theorem initial_valid (fuel : Nat) (value : CallerControl.Packet (Word 10) (Fin 4) (Word 10) (Word 10))
    (valid : admissible value) : CallerControl.Valid invariant fuel (id value.1, value.2) := by
  rcases value with ⟨value | pending, saved⟩ <;> exact valid

private theorem controller_refines (fuel : Nat) : Interactive.RefinesOn admissible port .unit
    ((CallerStep.next layout).prod word (by decide)) (CallerStep.output layout)
    (fun value => CallerControl.start advance handlerSource fuel value) (controller fuel) :=
  CallerControl.program_refines layout port advance continuation (by decide) invariant ready handler_refines available preserves
    (CallerStep.next layout) id initialCode (by decide) (by decide) fuel admissible (initial_valid fuel)

private theorem handler_time : Interactive.TimeBoundOn ready port .unit (CallerStep.request layout) handler 46 :=
  (UniformQuery.forward_time 3 (by decide) (by decide) word (by decide)).on ready
private theorem continuation_time (value) : continuation.time value ≤ 1000 := by
  change continuation.time (0, ⟨(0 : Fin 4), (0 : Fin 1)⟩) ≤ 1000
  decide
private theorem initial_time (value) : initialCode.time value ≤ 0 := Nat.le_refl _

private theorem controller_time (fuel : Nat) : Interactive.TimeBoundOn admissible port .unit
    ((CallerStep.next layout).prod word (by decide)) (controller fuel) (644 + fuel * 2256) :=
  CallerControl.program_time layout port advance continuation (by decide) invariant ready handler_refines available handler_time continuation_time preserves
    (CallerStep.next layout) id initialCode (by decide) (by decide) fuel admissible (initial_valid fuel) 0 initial_time

private theorem handler_names : WordIO.NamesAccounted (handler.lower port) 3 :=
  (UniformQuery.forward_names 3 (by decide) (by decide) word).accounted
private theorem continuation_names : NamesAccounted continuation.code 3 :=
  (selectSlice_names 0 1 3).seq (inl_names word (CallerStep.pending layout) (by decide) (by decide)).accounted

example (fuel : Nat) : (controller fuel).lower port |>.DescriptionFits :=
  CallerControl.program_descriptionFits layout port advance continuation (by decide) handler (CallerStep.next layout) id initialCode
    (by decide) (by decide) (UniformQuery.forward_descriptionFits 3 (by decide) (by decide) word (by decide)) (by decide) fuel
example (fuel : Nat) : WordIO.NamesAccounted ((controller fuel).lower port) 3 :=
  CallerControl.program_names layout port advance continuation (by decide) handler (CallerStep.next layout) id initialCode
    (by decide) (by decide) (by decide) handler_names continuation_names (skip_names 3) fuel
example (fuel : Nat) : ((controller fuel).lower port).descriptionWords ≤
    CallerControl.programWords layout port advance continuation handler (CallerStep.next layout) id initialCode fuel :=
  CallerControl.program_words layout port advance continuation (by decide) handler (CallerStep.next layout) id initialCode (by decide) (by decide) fuel

-- The source has an unbounded Nat query interface. Only pending states whose
-- range is represented by the port are admitted; immediate results are arbitrary
-- words. The certificate implements the original source computation in one query.
private def machineStep (value : Word 10 ⊕ Word 10) : Word 10 ⊕ unifSpec.toPFunctor.Obj (Word 10 ⊕ Word 10) :=
  match value with
  | .inl result => .inl result
  | .inr pending => .inr ⟨pending.toNat, fun _ => .inl pending⟩
private def machine : OracleMachine unifSpec (Word 10 ⊕ Word 10) (Word 10) := ofStep machineStep id
private def sourceProgram (value : Word 10 ⊕ Word 10) : ProbComp (Word 10) :=
  match value with
  | .inl result => pure result
  | .inr pending => unifSpec.query pending.toNat >>= fun _ => pure pending
private theorem implements : machine.ImplementsWithin sourceProgram 1 := by
  intro value
  cases value <;> simp [machine, sourceProgram, PFunctor.DynSystem.DynComputation.run, unroll, machineStep, bind_pure_comp]
  rfl

private def original : QueryImpl unifSpec (StateT (Word 10) ProbComp) :=
  fun position saved => (fun answer => (answer, saved)) <$> unifSpec.query position
private def stateView (value : Fin 4 × Word 10) : machine.State := .inr value.2
private def inputView (value : Word 10 ⊕ (Fin 4 × Word 10)) : Word 10 ⊕ Word 10 := value.map id Prod.snd
private def replyMatches (q : Fin 4) (reply : UniformQuery.Reply 3) (answer : Fin (q.val + 1)) := reply = ⟨q, answer⟩

private theorem handler_matches (remaining : Nat) (value : CallerControl.Frame (Word 10) (Fin 4) (Word 10))
    (_ : invariant (remaining + 1) value) :
    Synchronizes (CallerMachine.replyRelation Fin.val id replyMatches value.1.1)
      (handlerSource (value.1.1, value.2)) ((original value.1.1.val).run value.2) := by
  change Synchronizes _ (queryBind value.1.1.val _) (queryBind value.1.1.val _)
  exact .query _ (fun _ => .pure ⟨rfl, rfl⟩)

private theorem advance_matches (remaining : Nat) (q : Fin 4) (c saved : Word 10)
    (valid : invariant (remaining + 1) ((q, c), saved))
    (next : Fin (q.val + 1) → machine.State) (view : machine.view (stateView (q, c)) = .inr ⟨q.val, next⟩)
    (reply : UniformQuery.Reply 3) (originalReply : Fin (q.val + 1)) (_ : replyMatches q reply originalReply) :
    CallerMachine.Matches machine Fin.val stateView (advance (c, reply)) (next originalReply) := by
  have canonical : machine.view (stateView (q, c)) = .inr ⟨q.val, fun _ => .inl c⟩ := by
    change c.toNat = q.val at valid
    simp only [machine, stateView, view_ofStep, machineStep, Sum.inr.injEq]
    rw [valid]
  rw [machine.next_eq_of_view_query view canonical]
  exact CallerMachine.Matches.returned (machine := machine) (query := Fin.val) (state := stateView)
    c (Sum.inl c) (by simp [machine, machineStep])

private theorem initial_matches (value : CallerControl.Packet (Word 10) (Fin 4) (Word 10) (Word 10))
    (valid : admissible value) : CallerMachine.Matches machine Fin.val stateView value.1 (machine.init (inputView value.1)) := by
  rcases value with ⟨value | ⟨q, c⟩, saved⟩
  · exact CallerMachine.Matches.returned (machine := machine) (query := Fin.val) (state := stateView)
      value (Sum.inl value) (by simp [machine, machineStep])
  · refine .pending q c (fun _ => .inl c) ?_
    change c.toNat = q.val at valid
    simp only [machine, stateView, view_ofStep, machineStep, Sum.inr.injEq]
    rw [valid]

private theorem source_observation (fuel : Nat) (value) (valid : admissible value) :
    CallerMachine.observe id <$> CallerControl.start advance handlerSource fuel value =
      (machine.runWithInput original fuel (inputView value.1)).run value.2 :=
  CallerMachine.start_eq_runWith machine Fin.val stateView id replyMatches advance handlerSource original invariant
    handler_matches advance_matches preserves fuel value (machine.init (inputView value.1)) (initial_valid fuel value valid)
    (initial_matches value valid)

private theorem compiled_observation (fuel : Nat) (tape : RandomTape 10) (value) (valid : admissible value)
    (before : State 10) (holds : ((CallerStep.next layout).prod word (by decide)).Holds value before) :
    (fun result => CallerMachine.observe id <$> Interactive.observe (CallerStep.output layout) result) <$>
      (controller fuel).execute port .unit tape before =
      some <$> (machine.runWithInput original fuel (inputView value.1)).run value.2 :=
  CallerMachine.program_observe machine Fin.val stateView id replyMatches advance handlerSource original invariant
    handler_matches advance_matches preserves layout port continuation (by decide) handler ready handler_refines available
    (CallerStep.next layout) id initialCode (by decide) (by decide) fuel admissible (initial_valid fuel) inputView initial_matches
    tape value valid before holds

private theorem source_program (value) (valid : admissible value) :
    CallerMachine.observe id <$> CallerControl.start advance handlerSource 1 value =
      (fun result => (some result.1, result.2)) <$> (simulateQ original (sourceProgram (inputView value.1))).run value.2 :=
  CallerMachine.start_eq_simulateQ machine Fin.val stateView id replyMatches advance handlerSource original invariant
    handler_matches advance_matches preserves 1 value (inputView value.1) (initial_valid 1 value valid)
    (initial_matches value valid) sourceProgram implements

private theorem compiled_source (tape : RandomTape 10) (value) (valid : admissible value)
    (before : State 10) (holds : ((CallerStep.next layout).prod word (by decide)).Holds value before) :
    (fun result => CallerMachine.observe id <$> Interactive.observe (CallerStep.output layout) result) <$>
      (controller 1).execute port .unit tape before =
      (fun result => some (some result.1, result.2)) <$> (simulateQ original (sourceProgram (inputView value.1))).run value.2 :=
  CallerMachine.program_observe_source machine Fin.val stateView id replyMatches advance handlerSource original invariant
    handler_matches advance_matches preserves layout port continuation (by decide) handler ready handler_refines available
    (CallerStep.next layout) id initialCode (by decide) (by decide) 1 admissible (initial_valid 1) inputView initial_matches
    sourceProgram implements tape value valid before holds

private theorem controller_memory (fuel : Nat) (tape : RandomTape 10) (value) (valid : admissible value)
    (before : State 10) (holds : ((CallerStep.next layout).prod word (by decide)).Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 10) (reached : some finished ∈ support ((controller fuel).execute port .unit tape before)) :
    ∃ execution : WordIO.Exec .unit tape ((controller fuel).lower port) before finished.state finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        (((controller fuel).lower port).staticWords registers buffers : Int) + between.liveMem (max buffers ((controller fuel).lower port).memBound) ≤
          5 * CallerControl.programWords layout port advance continuation handler (CallerStep.next layout) id initialCode fuel +
            12 + registers + 3 * buffers + before.liveMem buffers + (644 + fuel * 2256 : Nat) := by
  have certified := CallerControl.program_resources layout port advance continuation (by decide) invariant ready handler_refines available preserves
    (CallerStep.next layout) id initialCode (by decide) (by decide) fuel admissible (initial_valid fuel)
    46 1000 0 handler_time continuation_time initial_time 3 (by decide) handler_names continuation_names (skip_names 3)
    tape value valid before holds registers buffers initialRegisters initialBuffers finished reached
  obtain ⟨_, _, _, _, execution, bounded⟩ := certified
  refine ⟨execution, fun between visited => ?_⟩
  have memory := (bounded between visited).2.2.2
  have budget : CallerControl.timeBudget (CallerStep.next layout).encoding.words (CallerStep.width layout) 46 1000 0 fuel = 644 + fuel * 2256 := rfl
  rw [budget] at memory
  dsimp only [controller]
  omega

-- A second caller continues after every reply. This exercises repeated dispatch
-- and exposes the final pending packet when the supplied allowance is exhausted.
private def sampled (reply : UniformQuery.Reply 3) : Fin 4 :=
  ⟨reply.2.val, by have := reply.1.isLt; have := reply.2.isLt; omega⟩
private def adaptiveAdvance (value : Word 10 × UniformQuery.Reply 3) : Word 10 ⊕ (Fin 4 × Word 10) := .inr (sampled value.2, value.1)
private def adaptiveCode : Realizer .unit (CallerStep.resume layout) (CallerStep.next layout) adaptiveAdvance :=
  Assembly.realizer .unit (by decide) _ _ adaptiveAdvance [.literal 1, .read 0 2, .read 0 0] (by decide)
    rfl (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 3 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> simp [Assembly.Operand.Valid, size])
    (by
      intro value before holds
      have contents : before.bufs 0 = #[value.1, BitVec.ofNat 10 value.2.1.val, BitVec.ofNat 10 value.2.2.val] :=
        Array.toList_inj.mp holds.2.1
      change [1, (before.bufs 0)[2]?.getD 0, (before.bufs 0)[0]?.getD 0] = [1, BitVec.ofNat 10 value.2.2.val, value.1]
      rw [contents]
      rfl)
private def adaptiveController (fuel : Nat) := CallerControl.program layout port adaptiveAdvance adaptiveCode (by decide) handler
  (CallerStep.next layout) id initialCode (by decide) (by decide) fuel
private theorem adaptive_refines (fuel : Nat) : Interactive.RefinesOn (fun _ => True) port .unit
    ((CallerStep.next layout).prod word (by decide)) (CallerStep.output layout)
    (fun value => CallerControl.start adaptiveAdvance handlerSource fuel value) (adaptiveController fuel) :=
  CallerControl.program_refines layout port adaptiveAdvance adaptiveCode (by decide) (fun _ _ => True) ready handler_refines
    (by intros; trivial) (by intros; trivial) (CallerStep.next layout) id initialCode (by decide) (by decide) fuel (fun _ => True)
    (by intro value _; rcases value with ⟨value | pending, saved⟩ <;> trivial)

private def execute (fuel : Nat) (value : CallerControl.Packet (Word 10) (Fin 4) (Word 10) (Word 10))
    (replies : List (Word 10)) (active : Interactive.Code 10 := controller fuel) :=
  let initial := ((CallerStep.next layout).prod word (by decide)).initial value
  let before := { initial with bufs := fun b => if b = 200 then #[91] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 200 then 99 else initial.regs r
                               tapePos := 9 }
  (WordIO.run .unit RandomTape.zero 20000 (active.lower port) before replies).map
    (fun finished => (finished.state.bufs 0, finished.trace, finished.remaining,
      finished.state.bufs 200, finished.state.caps 200, finished.state.regs 200, finished.state.tapePos))

open Lean in
run_cmd do
  unless execute 0 (.inl 7, 88) [55] == some (#[0, 7, 0, 88], [], [55], #[91], 4, 99, 9) do
    throwError "controller failed to return an initial result with zero fuel"
  unless execute 0 (.inr (3, 3), 88) [55] == some (#[1, 3, 3, 88], [], [55], #[91], 4, 99, 9) do
    throwError "controller cutoff did not retain a distinct pending packet"
  unless execute 1 (.inr (3, 3), 88) [3, 1, 55] == some (#[0, 3, 0, 88],
      [.output 3, .invoke, .input 3, .input 1], [55], #[91], 4, 99, 9) do
    throwError "controller query-to-result transition failed"
  unless execute 2 (.inr (3, 3), 88) [3, 1, 55] == some (#[0, 3, 0, 88],
      [.output 3, .invoke, .input 3, .input 1], [55], #[91], 4, 99, 9) do
    throwError "controller failed to stop early after the result"
  unless execute 2 (.inr (3, 77), 88) [3, 2, 2, 1, 55] (adaptiveController 2) == some (#[1, 1, 77, 88],
      [.output 3, .invoke, .input 3, .input 2, .output 2, .invoke, .input 2, .input 1], [55], #[91], 4, 99, 9) do
    throwError "controller repeated-call path lost state or failed to expose cutoff"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CallerControl.program_refines, ``CallerControl.program_time, ``CallerControl.program_words,
      ``CallerControl.program_descriptionFits, ``CallerControl.program_names, ``CallerControl.program_resources,
      ``CallerMachine.start_synchronizes, ``CallerMachine.start_eq_runWith, ``CallerMachine.start_eq_simulateQ,
      ``CallerMachine.program_observe, ``CallerMachine.program_observe_source,
      ``controller_refines, ``controller_time, ``controller_memory, ``compiled_observation,
      ``source_observation, ``source_program, ``compiled_source, ``adaptive_refines, ``implements] do
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperCallerControl
