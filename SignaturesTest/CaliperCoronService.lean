import Signatures.Runtime.Caliper.CoronServiceBounds
import Signatures.Runtime.Caliper.CoronServiceSource
import Signatures.Runtime.Caliper.CoronTerminalBounds
import Lean

/-! Whole-service execution with real sampling and word arithmetic. These are
wiring tests, not a curve instance. Sequential calls pass the decoded store to
the next request; the test harness's boundary encoding is not generated caller
code. The generic source theorem separately covers fields and group modules. -/
namespace SignaturesTest.CaliperCoronService
open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

private instance : SMul (Fin 4) (Word 16) := ⟨fun scalar point => BitVec.ofNat 16 scalar.val * point⟩
private def layout : CoronService.Layouts 16 Nat (Fin 4) (Word 16) 255 (1 : Fin 256) where
  cache := {
    key := Layout.counter 16 256 (by decide) (by decide)
    value := UniformSampling.output 255 (by decide) (by decide) (3 : Fin 256)
    capacityPred := 1
    wordFits := by decide
    countFits := by decide
    storageFits := by decide }
  point := Layout.all (wordRepresentation 16 (by decide))
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
    (fun value => (BitVec.ofNat 16 value.val.1.val, value.val.2)) (fun _ => rfl)).viewOutput layout.point.representation
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

private theorem within : Interactive.Within layout.port (layout.input default) layout.output
    (CoronService.codeBudget layout routines sampler) (CoronService.memoryBudget layout default routines sampler)
    (CoronService.timeBudget layout routines sampler) (fun value => CoronService.denote layout default routines sampler value.val) :=
  CoronService.within layout default routines sampler

private def empty : layout.service.store.Value := ⟨((7, 11, 17), [], [], []), by
  dsimp only [BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
    BLSRecord.Layouts.transcript, BLSRecord.Layouts.log, BLSRecord.Layouts.entry,
    Layout.prod, Layout.boundedList, Layout.counter, Layout.all,
    CacheLayout.lookup, LookupLayout.table, LookupLayout.entry,
    CoronService.Layouts.service, CoronService.Layouts.response, CoronResponse.Layouts.config,
    CoronResponse.Layouts.points, CacheLayout.coinValues, CoronSampling.output, UniformSampling.output,
    Finite.layout, layout]
  decide⟩
private def key : layout.cache.key.Value := ⟨5, by change 5 < 256; decide⟩
private def hash : BLSCallerPackets.Request layout.service 255 := .inr (.inl key)
private def sign : BLSCallerPackets.Request layout.service 255 := .inr (.inr key)
private def fullLog : layout.service.store.Value :=
  ⟨((7, 11, 17), [(5, (3, 1))], [], [(5, 33), (5, 33)]), by
    dsimp only [BLSReply.Layouts.store, BLSReply.Layouts.cacheLogs, BLSReply.Layouts.records,
      BLSRecord.Layouts.transcript, BLSRecord.Layouts.log, BLSRecord.Layouts.entry,
      Layout.prod, Layout.boundedList, Layout.counter, Layout.all,
      CacheLayout.lookup, LookupLayout.table, LookupLayout.entry,
      CoronService.Layouts.service, CoronService.Layouts.response, CoronResponse.Layouts.config,
      CoronResponse.Layouts.points, CacheLayout.coinValues, CoronSampling.output, UniformSampling.output,
      Finite.layout, layout]
    decide⟩
example : (layout.input default).valid (hash, empty) := by
  change BLSCallerPackets.ready layout.service (layout.pairDefault default) 255 (hash, empty)
  dsimp [BLSCallerPackets.ready, hash, empty, BLSReply.Layouts.guard, CacheLayout.admissible]
  decide
example : (layout.input default).valid (sign, empty) := by
  change BLSCallerPackets.ready layout.service (layout.pairDefault default) 255 (sign, empty)
  dsimp [BLSCallerPackets.ready, sign, empty, BLSReply.Layouts.guard, CacheLayout.admissible]
  decide
example : ¬(layout.input default).valid (sign, fullLog) := by
  change ¬BLSCallerPackets.ready layout.service (layout.pairDefault default) 255 (sign, fullLog)
  dsimp [BLSCallerPackets.ready, sign, fullLog, BLSReply.Layouts.guard, CacheLayout.admissible]
  decide
example : (layout.input default).valid (.inl 255, fullLog) := trivial

private def execute (request : BLSCallerPackets.Request layout.service 255)
    (saved : layout.service.store.Value) (replies : List (Word 16)) := do
  let initial := (BLSCallerPackets.input layout.service 255 layout.randomFits).initial (request, saved)
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 3 else initial.caps buffer
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 100000
    ((CoronService.code layout default routines sampler).lower layout.port) before replies
  let decoded ← (BLSCallerPackets.output layout.service 255 layout.randomFits).encoding.decode (result.state.bufs 0).toList
  pure (result, decoded)

private def observe (request : BLSCallerPackets.Request layout.service 255)
    (saved : layout.service.store.Value) (replies : List (Word 16)) := do
  let (result, decoded) ← execute request saved replies
  pure (BLSCallerHandler.replyValue layout.service 255 decoded.1, decoded.2.val, result.trace, result.remaining,
    result.state.bufs 200, result.state.caps 200, result.state.regs 200, result.state.tapePos,
    decide (result.time ≤ CoronService.timeBudget layout routines sampler))

private def hashThenSign (coin : Word 16) := do
  let (hashed, decoded) ← execute hash empty [3, 3, 1, coin, 42]
  let signed ← observe sign decoded.2 hashed.remaining
  pure (BLSCallerHandler.replyValue layout.service 255 decoded.1, hashed.trace, signed)

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

private theorem terminal_valid_iff (message : Nat) (fallback : Fin 4 × Fin 2)
    (entries : List (Nat × (Fin 4 × Fin 2))) (sigma X : Word 16) :
    (CoronTerminal.input layout).valid ((message, fallback, entries, ()), (sigma, X)) ↔
      (message < 256 ∧ entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256) ∧
        ((lookupValue message fallback entries).1 = false → entries.length ≤ 1) := by
  change (((message < 256 ∧ (True ∧ True) ∧
    (entries.length ≤ 2 ∧ ∀ entry ∈ entries, entry.1 < 256 ∧ (True ∧ True)) ∧ True) ∧
    ((lookupValue message fallback entries).1 = false → entries.length ≤ 1)) ∧ (True ∧ True)) ↔ _
  simp only [true_and, and_true]
private def finalFresh : (CoronTerminal.input layout).Value :=
  ⟨((5, (0, 1), [], ()), (100, 11)), by rw [terminal_valid_iff]; decide +kernel⟩
private def finalHit : (CoronTerminal.input layout).Value :=
  ⟨((5, (0, 0), [(5, (3, 1)), (6, (2, 0))], ()), (100, 11)), by rw [terminal_valid_iff]; decide +kernel⟩
private def finalShadowed : (CoronTerminal.input layout).Value :=
  ⟨((5, (3, 0), [(5, (0, 1)), (5, (3, 0))], ()), (100, 11)), by rw [terminal_valid_iff]; decide +kernel⟩
example : ¬(CoronTerminal.input layout).valid
    ((7, (0, 0), [(5, (3, 1)), (6, (2, 0))], ()), (100, 11)) := by
  rw [terminal_valid_iff]; decide +kernel

private theorem terminal_within : Interactive.Within layout.port (CoronTerminal.input layout) layout.point
    (CoronTerminal.codeBudget layout sampler terminalArithmetic) (CoronTerminal.memoryBudget layout sampler terminalArithmetic)
    (CoronTerminal.timeBudget layout sampler terminalArithmetic)
    (fun value => (fun result => value.val.2.1 - result.1.1 • value.val.2.2) <$>
      ((BLS.LazyAGM.Reduction.privateListOracle (M := Nat) (R := Fin 4 × Fin 2))
        (.inr value.val.1.1)).run value.val.1.2.2.1) :=
  CoronTerminal.within layout sampler terminalArithmetic

private def finish (value : (CoronTerminal.input layout).Value) (replies : List (Word 16)) := do
  let initial := (CoronTerminal.input layout).representation.initial value
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 3 else initial.caps buffer
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 100000
    ((CoronTerminal.code layout sampler terminalArithmetic).lower layout.port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining,
    result.state.bufs 200, result.state.caps 200, result.state.regs 200, result.state.tapePos,
    decide (result.time ≤ CoronTerminal.timeBudget layout sampler terminalArithmetic))

open Lean in
run_cmd do
  let draws : List (WordIO.Event 16) :=
    [.output 3, .invoke, .input 3, .input 3, .output 1, .invoke, .input 1, .input 0]
  unless observe hash empty [3, 3, 1, 0, 42] ==
      some (.inr 38, ((7, 11, 17), [(5, (3, 0))], [(5, 38)], []), draws, [42], #[77], 3, 99, 7, true) do
    throwError "fresh hash lost the paired entry, transcript, challenge points or private frame"
  unless hashThenSign 0 == some (.inr 38, draws,
      (.inr 0, ((7, 11, 17), [(5, (3, 0))], [(5, 38)], [(5, 0)]), [], [42], #[77], 3, 99, 7, true)) do
    throwError "cached zero-coin signing resampled, changed its coin, or lost the hash log"
  let ordinaryDraws : List (WordIO.Event 16) :=
    [.output 3, .invoke, .input 3, .input 3, .output 1, .invoke, .input 1, .input 1]
  unless observe sign empty [3, 3, 1, 1, 42] ==
      some (.inr 33, ((7, 11, 17), [(5, (3, 1))], [], [(5, 33)]), ordinaryDraws, [42], #[77], 3, 99, 7, true) do
    throwError "fresh signing failed to sample and record its entry independently of hashing"
  unless hashThenSign 1 == some (.inr 21, ordinaryDraws,
      (.inr 33, ((7, 11, 17), [(5, (3, 1))], [(5, 21)], [(5, 33)]), [], [42], #[77], 3, 99, 7, true)) do
    throwError "ordinary cached signing did not reuse its scalar and preserve both logs"
  unless observe (.inl 255) fullLog [255, 254, 42] ==
      some (.inl (255, 254), fullLog.val, [.output 255, .invoke, .input 255, .input 254],
        [42], #[77], 3, 99, 7, true) do
    throwError "random forwarding changed the persistent store or dependent reply range"
  unless (execute hash empty [3, 3]).isNone do
    throwError "fresh hashing completed without its coin reply"
  unless finish finalFresh [3, 3, 1, 0, 42] == some (#[67], draws, [42], #[77], 3, 99, 7, true) do
    throwError "fresh terminal extraction did not return sigma minus rho times X"
  unless finish finalFresh [3, 3, 1, 1, 42] == some (#[67], ordinaryDraws, [42], #[77], 3, 99, 7, true) do
    throwError "terminal extraction improperly depends on the coin branch"
  unless finish finalHit [42] == some (#[67], [], [42], #[77], 3, 99, 7, true) do
    throwError "full-cache terminal hit resampled or changed the cached scalar"
  unless finish finalShadowed [42] == some (#[100], [], [42], #[77], 3, 99, 7, true) do
    throwError "terminal lookup ignored the first binding or mishandled zero scalar"
  unless (finish finalFresh [3, 3]).isNone do
    throwError "terminal sampling omitted the source computation's coin draw"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CoronService.refines, ``CoronService.time_bound, ``CoronService.code_words,
      ``CoronService.names, ``CoronService.descriptionFits, ``CoronService.within,
      ``CoronService.denote_source, ``CoronService.denote_native, ``CoronService.ready_of_reserved,
      ``CoronService.reserved_after, ``within, ``Coron.Paired.finish_hash, ``Coron.Paired.reduction_finish,
      ``CoronTerminal.extract, ``CoronTerminal.extract_bounded, ``CoronTerminal.extract_names,
      ``CoronTerminal.refines, ``CoronTerminal.source_eq, ``CoronTerminal.time_bound,
      ``CoronTerminal.code_words, ``CoronTerminal.names, ``CoronTerminal.descriptionFits,
      ``CoronTerminal.within, ``CoronTerminal.within_finish, ``terminal_within] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperCoronService
