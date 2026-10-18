import Signatures.Runtime.Caliper.OracleCall
import Signatures.Runtime.Caliper.Words
import Lean

open Caliper Signatures.Runtime.CaliperBackend

namespace SignaturesTest.CaliperWordIO

private def word := wordRepresentation 8 (by decide)
private def pair := word.prod word (by decide)
private def triple := pair.prod word (by decide)
private def initial : State 8 :=
  let state := pair.initial (7, 11)
  { state with
    bufs := fun buffer => if buffer = 7 then #[99] else state.bufs buffer
    caps := fun buffer => if buffer = 7 then 1 else state.caps buffer
    tapePos := 42 }

-- This checks actual instructions, I/O order, exact charges, caller framing,
-- unread input preservation, and independence from the private random tape.
private def exchangeRun := WordIO.run .unit RandomTape.zero 2 (WordIO.exchange 2 3) initial [13, 17, 19, 23]
example : exchangeRun.map (fun result => ((result.state.bufs 0, result.state.bufs 7),
      (result.time, result.net, result.peak))) = some ((#[13, 17, 19], #[99]), (16, 1, 1)) := by decide
example : exchangeRun.map (fun result => (result.state.regs 0, result.state.tapePos)) = some (0, 42) := by decide
example : exchangeRun.map (fun result => (result.trace, result.remaining)) =
    some ([.output 7, .output 11, .invoke, .input 13, .input 17, .input 19], [23]) := by decide

-- Freeing the old request capacity is reflected in signed net/peak accounting.
example : (WordIO.run .unit RandomTape.zero 2 (WordIO.exchange 3 1)
    (triple.initial ((3, 5), 7)) [11]).map
    (fun result => (result.state.bufs 0, result.time, result.net, result.peak)) =
    some (#[11], 13, -2, 0) := by decide

-- A zero-width exchange still invokes the oracle exactly once. This matters for
-- stateful oracles even when their input and output carry no words.
example : (WordIO.run (w := 8) .unit RandomTape.zero 2 (WordIO.exchange 0 0) (State.init 8) []).map
    (fun result => (result.trace, result.time, result.net, result.peak)) =
    some ([.invoke], 1, 0, 0) := by decide

example : (WordIO.exchange (w := 8) 2 3).descriptionWords = 62 := by decide
example : ¬ (WordIO.exchange (w := 8) 2 256).DescriptionFits := by
  intro fits
  have invalid := fits 256 (by decide)
  norm_num at invalid

-- Missing input, missing request storage, and a full reply buffer cannot be
-- replaced by a free mathematical value installation.
example : (WordIO.run .unit RandomTape.zero 2 (WordIO.exchange 2 3) initial [13, 17]).isNone = true := by decide
example : (WordIO.run .unit RandomTape.zero 2 (WordIO.exchange 3 1) initial [13]).isNone = true := by decide
example : (WordIO.run .unit RandomTape.zero 2 (WordIO.receive 0 1) initial [13]).isNone = true := by decide

private def counter : BoundedSource.Layout 8 Nat := BoundedSource.Layout.counter 8 16 (by decide) (by decide)
private def resultOrState := counter.sum counter (by decide) (by decide)
private def continueStep : BoundedSource.Implementation .unit counter resultOrState (fun n => Sum.inr n) where
  preserves _ valid := valid
  program := (inrRealizer .unit (by decide) counter.representation counter.representation (by decide) (by decide)).viewOutput
    resultOrState.representation (fun value => ⟨Sum.inr value.val, value.property⟩) (fun _ => rfl)
private def sourceLoop := BoundedSource.Implementation.loop (by decide) counter counter (by decide) (by decide)
  continueStep (BoundedSource.Implementation.identity counter (by decide)) 2

-- The source uses Nat, but only represented reachable values enter the machine.
example : ¬ counter.valid 16 := by change ¬ 16 < 16; decide
example : (Caliper.run .unit RandomTape.zero 1000 sourceLoop.program.code
    (counter.representation.initial ⟨7, by change 7 < 16; decide⟩)).map
    (fun (state, time, _, _) => (counter.representation.encoding.decode (state.bufs 0).toList, time)) =
    some (some ⟨7, by change 7 < 16; decide⟩, 50) := by decide

private def smallSpec : OracleSpec (Fin 4) := fun _ => Fin 4
private def smallRequest := Representation.fin 8 4 (by decide) (by decide)
private def smallReply : Representation 8 (Σ i, smallSpec.Range i) :=
  (smallRequest.prod smallRequest (by decide)).transport
    { toFun := fun value => (value.1, value.2)
      invFun := fun value => ⟨value.1, value.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

-- The external oracle sees the executed request; the returned dependent packet
-- includes that position and is physically stored by the adapter.
example : ((simulateQ (fun position : Fin 4 => (pure (position + 1) : Id (Fin 4)))
    (WordIO.oracleCall smallSpec .unit RandomTape.zero smallRequest smallReply
      (smallRequest.initial 2))).run).map
    (fun result => (result.state.bufs 0, result.time, result.trace)) =
    some (#[2, 3], 10, [.output 2, .invoke, .input 2, .input 3]) := by decide

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BoundedSource.Implementation.exec, ``BoundedSource.loop_preserves,
      ``BoundedSource.liftedLoop_value, ``BoundedSource.Implementation.loop,
      ``WordIO.Exec.frame_reg, ``WordIO.Exec.frame_buf, ``WordIO.Exec.wellFormed_preserved,
      ``WordIO.Exec.tapePos_eq, ``WordIO.send_exec, ``WordIO.receive_exec,
      ``WordIO.exchange_exec, ``WordIO.exchange_frame, ``WordIO.exchange_descriptionFits,
      ``WordIO.exchange_descriptionWords, ``WordIO.exchangeTime_unit,
      ``WordIO.run_sound, ``WordIO.Exec.run_eventually, ``WordIO.Exec.run_atFuel,
      ``WordIO.exchange_run, ``WordIO.oracleCall_eq, ``WordIO.oracleCall_value] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperWordIO
