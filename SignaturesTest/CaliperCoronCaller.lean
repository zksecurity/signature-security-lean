import Signatures.Runtime.Caliper.CoronFullSource
import Signatures.Runtime.Caliper.CoronCallerPresentation
import Lean

/-! Execute the complete Coron caller/service/extractor with actual local
attacker code. Word arithmetic is a wiring fixture, not a curve instance. -/
namespace SignaturesTest.CaliperCoronCaller
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

private instance : SMul (Fin 4) (Word 32) := ⟨fun scalar point => BitVec.ofNat 32 scalar.val * point⟩
private def layout : CoronService.Layouts 32 Nat (Fin 4) (Word 32) 255 (1 : Fin 256) where
  cache := {
    key := Layout.counter 32 256 (by decide) (by decide)
    value := UniformSampling.output 255 (by decide) (by decide) (3 : Fin 256)
    capacityPred := 1
    wordFits := by decide
    countFits := by decide
    storageFits := by decide }
  point := Layout.all (wordRepresentation 32 (by decide))
  randomFits := by decide
  responseFits := by decide
  pairFits := by decide
  capacityPred := 1
  countFits := by decide
  serviceFits := by decide
private def default : layout.cache.value.Value := ⟨0, trivial⟩

private def scale : Implementation .unit layout.response.scaleArgs layout.point (fun value => value.1 • value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul layout.cache.wordFits).viewInput layout.response.scaleArgs.representation
    (fun value => (BitVec.ofNat 32 value.val.1.val, value.val.2)) (fun _ => rfl)).viewOutput layout.point.representation
      (fun value => ⟨value.val.1 • value.val.2, trivial⟩) (fun _ => rfl)
private def add : Implementation .unit layout.response.points layout.point (fun value => value.1 + value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .add layout.cache.wordFits).viewInput layout.response.points.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.point.representation
      (fun value => ⟨value.val.1 + value.val.2, trivial⟩) (fun _ => rfl)
private def routines : CoronService.Routines layout where
  scale := scale
  add := add
  zeroValid := trivial
  scaleTime := 6
  scaleWords := 27
  addTime := 6
  addWords := 27
  scaleBound := ⟨fun _ => le_rfl, le_rfl⟩
  addBound := ⟨fun _ => le_rfl, le_rfl⟩
  slots := 3
  scaleNames := by constructor <;> decide
  addNames := by constructor <;> decide
  reserve := by decide
private def sampler : CoronService.Sampler layout where
  code := UniformSampling.code 255 (by decide) (by decide) (3 : Fin 256)
  source := UniformSampling.source 255 (by decide) (by decide) (3 : Fin 256)
  correct := UniformSampling.refines 255 (by decide) (by decide) (3 : Fin 256)
  law := UniformSampling.uniform 255 (by decide) (by decide) (3 : Fin 256)
  time := 26
  words := 125
  slots := 3
  timeBound := UniformSampling.time_bound 255 (by decide) (by decide) (3 : Fin 256)
  codeBound := UniformSampling.code_words 255 (by decide) (by decide) (3 : Fin 256)
  names := UniformSampling.names 255 (by decide) (by decide) (3 : Fin 256)
  descriptionFits := UniformSampling.descriptionFits 255 (by decide) (by decide) (3 : Fin 256)
  reserve := by decide


private def empty : layout.service.store.Value := ⟨((7, 11, 17), [], [], []), by
  dsimp only [BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
    BLSRecord.Layouts.transcript, BLSRecord.Layouts.log, BLSRecord.Layouts.entry,
    Layout.prod, Layout.boundedList, Layout.counter, Layout.all,
    CacheLayout.lookup, LookupLayout.table, LookupLayout.entry,
    CoronService.Layouts.service, CoronService.Layouts.response, CoronResponse.Layouts.config,
    CoronResponse.Layouts.points, CacheLayout.coinValues, CoronSampling.output, UniformSampling.output,
    Finite.layout, layout]
  decide⟩

private def subtraction : Implementation .unit layout.response.points layout.point (fun value => value.1 - value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub layout.cache.wordFits).viewInput layout.response.points.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.point.representation
      (fun value => ⟨value.val.1 - value.val.2, trivial⟩) (fun _ => rfl)
private def terminalArithmetic : CoronTerminal.Arithmetic layout where
  scale := scale
  sub := subtraction
  scaleTime := 6
  scaleWords := 27
  subTime := 6
  subWords := 27
  scaleBound := ⟨fun _ => le_rfl, le_rfl⟩
  subBound := ⟨fun _ => le_rfl, le_rfl⟩
  slots := 3
  scaleNames := by constructor <;> decide
  subNames := by constructor <;> decide
  reserve := by decide


private def word := wordRepresentation 32 (by decide)
private def requestRep := BLSCallerPackets.request layout.service 255 layout.randomFits
private def inputRep := requestRep.prod word (by decide)
private def callerLayout : CoronCaller.Layouts layout (Word 32) (BLSCallerPackets.Request layout.service 255 × Word 32) where
  state := word
  input := inputRep
  callerFits := by decide
  inputFits := by decide
private def makeForgery (sigma : Word 32) : callerLayout.Forgery := ⟨(7, sigma), by
  change 7 < 256 ∧ True
  decide⟩
private def initial (value : BLSCallerPackets.Request layout.service 255 × Word 32) : callerLayout.Next := .inr value
private def initialCode : Realizer .unit inputRep (CallerStep.next callerLayout.control) initial :=
  inrRealizer .unit (by decide) (CoronTerminalFrame.forgery layout).representation
    (CallerStep.pending callerLayout.control) (by decide) (by decide)
private def advance (value : Word 32 × callerLayout.Reply) : callerLayout.Next := .inl (makeForgery value.1)
private def continuation : Realizer .unit (CallerStep.resume callerLayout.control) (CallerStep.next callerLayout.control) advance :=
  Assembly.realizer .unit (by decide) _ _ advance
    [.literal 0, .literal 7, .read 0 0, .literal 0, .literal 0] (by decide) rfl
    (by simp [Assembly.Operand.NamesFit])
    (by
      intro value before holds operand member
      have size := Assembly.represented_size _ holds
      change (before.bufs 0).size = 4 at size
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [Assembly.Operand.Valid, size])
    (by
      intro value before holds
      have contents : (before.bufs 0).toList = [value.1] ++
          (BLSCallerPackets.reply layout.service 255 layout.randomFits).encoding.encode value.2 := holds.2.1
      have first := ListFold.reads_block [] [value.1]
        ((BLSCallerPackets.reply layout.service 255 layout.randomFits).encoding.encode value.2) before
        (by simpa only [List.nil_append] using contents)
      change [(before.bufs 0)[0]?.getD 0] = [value.1] at first
      have equal := List.singleton_inj.mp first
      change [0, 7, (before.bufs 0)[0]?.getD 0, 0, 0] = [0, 7, value.1, 0, 0]
      rw [equal])
private def caller : CoronCaller.Caller callerLayout where
  advance := advance
  continuation := continuation
  localNameFits := by decide
  initial := initial
  initialCode := initialCode
  initialNameFits := by decide
private def bounded : CoronCaller.Caller.Bounds callerLayout caller where
  stepTime := 40
  stepWords := 144
  initialTime := 40
  initialWords := 144
  step_time _ := Assembly.code_time_unit_le _
  step_words := Assembly.code_descriptionWords_le _
  initial_time value := inr_time _ _ (by decide) _ value
  initial_words := inr_words _ _ (by decide) _
  slots := 3
  step_names := Assembly.code_namesAccounted _ _ (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])
  initial_names := (inr_names _ _ (by decide) _).accounted
private def invariant (fuel : Nat) : CoronCaller.Caller.Invariant callerLayout caller fuel where
  domain _ _ := True
  advance _ _ _ _ _ _ _ := trivial
  initial _ := trivial
private def fallback : layout.point.Value := ⟨999, trivial⟩
private theorem within (fuel : Nat) : Interactive.Within layout.port (callerLayout.admitted fuel) layout.point
    (CoronCaller.codeBudget layout callerLayout routines sampler terminalArithmetic caller bounded fuel)
    (CoronCaller.memoryBudget layout callerLayout routines sampler terminalArithmetic caller bounded fuel)
    (CoronCaller.timeBudget layout callerLayout routines sampler terminalArithmetic caller bounded fuel)
    (fun value => Subtype.val <$> CoronCaller.denote layout callerLayout default routines sampler terminalArithmetic caller fuel fallback value.val) :=
  CoronCaller.within layout callerLayout default routines sampler terminalArithmetic caller bounded fuel fallback (invariant fuel)
    (by unfold CoronCaller.addressBound; decide +kernel)
private theorem full_within (fuel : Nat) (small : fuel ≤ 1) : Interactive.Within layout.port (CoronFull.challenge layout callerLayout) layout.point
    (CoronFull.codeBudget layout callerLayout routines sampler terminalArithmetic caller bounded fuel)
    (CoronFull.memoryBudget layout callerLayout routines sampler terminalArithmetic caller bounded fuel)
    (CoronFull.timeBudget layout callerLayout routines sampler terminalArithmetic caller bounded fuel)
    (fun value => Subtype.val <$> CoronFull.denote layout callerLayout default routines sampler terminalArithmetic caller fuel fallback value) :=
  CoronFull.within layout callerLayout default routines sampler terminalArithmetic caller bounded fuel fallback (invariant fuel)
    (by change fuel + 1 ≤ 2; omega) (by change fuel ≤ 2; omega)
    (by unfold CoronCaller.addressBound; decide +kernel)

private def hash (message : Fin 256) : callerLayout.Request := .inr (.inl ⟨message.val, message.isLt⟩)
private def sign (message : Fin 256) : callerLayout.Request := .inr (.inr ⟨message.val, message.isLt⟩)

-- The same actual local instructions acquire their source presentation from
-- termination. Wrapping the admitted input changes only its mathematical type.
private def sourceKey := Layout.all inputRep
private def sourceLayout : CoronCaller.Layouts layout (Word 32) sourceKey.Value where
  state := word
  input := sourceKey.representation
  callerFits := by decide
  inputFits := by decide
private def sourceCaller : CoronCaller.Caller sourceLayout where
  advance := caller.advance
  continuation := caller.continuation
  localNameFits := caller.localNameFits
  initial := fun input => caller.initial input.val
  initialCode := caller.initialCode.viewInput sourceKey.representation Subtype.val (fun _ => rfl)
  initialNameFits := caller.initialNameFits
private theorem allPoints (point : Word 32) : layout.point.valid point := trivial
private theorem sourceTerminates :
    CoronCaller.Caller.Terminates sourceKey sourceLayout allPoints sourceCaller 1 := by
  intro input answer
  trivial
private def sourceFallback : sourceKey.Value := ⟨(hash 0, 0), trivial⟩
private noncomputable def sourceWitness :=
  CoronCaller.Caller.Correspondence.ofCaller sourceKey sourceLayout allPoints sourceCaller sourceTerminates sourceFallback
private theorem sourceWitness_eq (input : sourceKey.Value) : sourceWitness.source input.val =
    (do
      let _ ← (BLS.ROM.advSpec Nat (Word 32)).query (BLSCallerHandler.query layout.service 255 input.val.1)
      pure (makeForgery input.val.2)) := by
  have implemented := CoronCaller.Caller.Correspondence.ofCaller_run sourceKey sourceLayout allPoints
    sourceCaller sourceTerminates sourceFallback input
  change some <$> (do
      let _ ← (BLS.ROM.advSpec Nat (Word 32)).query (BLSCallerHandler.query layout.service 255 input.val.1)
      pure (makeForgery input.val.2) : OracleComp (BLS.ROM.advSpec Nat (Word 32)) callerLayout.Forgery) =
    some <$> sourceWitness.source input.val at implemented
  have observed := congrArg (fun computation : OracleComp (BLS.ROM.advSpec Nat (Word 32)) (Option callerLayout.Forgery) =>
    (fun result => result.getD (makeForgery 0)) <$> computation) implemented
  simpa using observed.symm

example (request : callerLayout.Request) (sigma : Word 32) : callerLayout.ready 1 ((request, sigma), empty) := by
  change 0 + 1 + 1 ≤ 2 ∧ 0 + 0 + 1 ≤ 2
  decide
example (request : callerLayout.Request) (sigma : Word 32) : ¬callerLayout.ready 2 ((request, sigma), empty) := by
  change ¬(0 + 2 + 1 ≤ 2 ∧ 0 + 0 + 2 ≤ 2)
  decide

private def run {T : Type} (input : Representation 32 T) (program : Interactive.Code 32) (budget : Nat)
    (value : T) (replies : List (Word 32)) := do
  let initial := input.initial value
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 3 else initial.caps buffer
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 500000
    (program.lower layout.port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining,
    result.state.bufs 200, result.state.caps 200, result.state.regs 200, result.state.tapePos,
    (List.range 32).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ budget))
private def execute (fuel : Nat) (request : callerLayout.Request) (sigma : Word 32) :=
  run callerLayout.incoming (CoronCaller.code layout callerLayout default routines sampler terminalArithmetic caller fuel fallback)
    (CoronCaller.timeBudget layout callerLayout routines sampler terminalArithmetic caller bounded fuel) ((request, sigma), empty)
private def executeFull (fuel : Nat) (request : callerLayout.Request) (sigma : Word 32) :=
  run (CoronFull.challenge layout callerLayout).representation
    (CoronFull.code layout callerLayout default routines sampler terminalArithmetic caller fuel fallback)
    (CoronFull.timeBudget layout callerLayout routines sampler terminalArithmetic caller bounded fuel)
    ⟨((request, sigma), ⟨(7, 11, 17), trivial, trivial, trivial⟩), trivial⟩
private def events (values : List (Word 32 × Word 32)) : List (WordIO.Event 32) :=
  values.flatMap (fun (bound, value) => [.output bound, .invoke, .input bound, .input value])
private def wire (values : List (Word 32 × Word 32)) := values.flatMap (fun (bound, value) => [bound, value])

open Lean in
run_cmd do
  for (fuel, request, sigma, samples, expected) in [
      (1, hash 5, 100, [(3, 3), (1, 0), (3, 2), (1, 1)], 78),
      (1, sign 5, 100, [(3, 3), (1, 1), (3, 2), (1, 0)], 78),
      (1, hash 7, 100, [(3, 3), (1, 0)], 67),
      (1, sign 7, 100, [(3, 3), (1, 1)], 67),
      (1, hash 7, 200, [(3, 3), (1, 1)], 167),
      (1, .inl 255, 100, [(255, 254), (3, 2), (1, 1)], 78),
      (0, hash 5, 100, [], 999)] do
    unless execute fuel request sigma (wire samples ++ [42]) ==
        some (#[expected], events samples, [42], #[77], 3, 99, 7, true, true) do
      throwError "composed Coron caller failed at fuel {fuel}, expected {expected}"
    unless executeFull fuel request sigma (wire samples ++ [42]) ==
        some (#[expected], events samples, [42], #[77], 3, 99, 7, true, true) do
      throwError "full Coron program failed at fuel {fuel}, expected {expected}"
  unless (execute 1 (hash 5) 100 [3, 3, 1, 0, 3, 2]).isNone do
    throwError "composed caller finished without the final message's coin"
  unless (executeFull 1 (hash 5) 100 [3, 3, 1, 0, 3, 2]).isNone do
    throwError "full Coron program finished without the final message's coin"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CoronCaller.Layouts.finish_input, ``CoronCaller.Layouts.reserved,
      ``CoronCaller.called_postcondition, ``CoronCaller.called_ready, ``CoronCaller.controller_refines,
      ``CoronCaller.refines, ``CoronCaller.code_words, ``CoronCaller.names, ``CoronCaller.descriptionFits,
      ``CoronCaller.time_bound, ``CoronCaller.within, ``CoronCaller.called_source,
      ``CoronCaller.finish_source, ``CoronCaller.denote_source, ``CoronCaller.original_simulation,
      ``CoronCaller.source_eq, ``CoronCaller.within_source, ``within,
      ``CoronFull.start_ready, ``CoronFull.refines, ``CoronFull.code_words, ``CoronFull.names,
      ``CoronFull.descriptionFits, ``CoronFull.time_bound, ``CoronFull.within,
      ``CoronFull.source_eq, ``CoronFull.within_source, ``CoronFull.source_original, ``CoronFull.within_original, ``full_within,
      ``CoronCaller.Caller.Invariant.ofTerminates, ``CoronCaller.Caller.Correspondence.ofCaller,
      ``CoronCaller.Caller.Correspondence.ofCaller_run, ``sourceTerminates, ``sourceWitness_eq] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperCoronCaller
