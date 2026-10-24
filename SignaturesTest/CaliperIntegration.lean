import Proofs.Runtime.Caliper
import Lean

open Caliper Signatures.Runtime.CaliperBackend

namespace SignaturesTest.CaliperIntegration

private def word := wordRepresentation 8 (by decide)
private def pair := word.prod word (by decide)
private def nested := word.prod pair (by decide)
private def tagged := word.sum pair (by decide) (by decide)
private def list := word.boundedList 3 (by decide) (by decide)

-- Out-of-range counters, tags and lengths are rejected by the specification
-- decoder. Padding and unused list slots still occupy physical storage.
example : (Encoding.fin 8 10 (by decide)).decode [10] = none := by decide
example : (Encoding.fin 8 10 (by decide)).decode [9] = some ⟨9, by decide⟩ := by decide
example : tagged.encoding.encode (.inl 42) = [0, 42, 0] := by decide
example : tagged.encoding.decode [2, 42, 0] = none := by decide
example : tagged.encoding.decode [1, 42] = none := by decide
example : tagged.encoding.decode [1, 42, 99] = some (.inr (42, 99)) := by decide
example : list.encoding.encode ⟨[7, 11], by decide⟩ = [2, 7, 11, 0] := by decide
example : list.encoding.decode [4, 7, 11, 13] = none := by decide
example : list.encoding.decode [2, 7, 11] = none := by decide
example : list.encoding.decode (list.encoding.encode ⟨[7, 11, 13], by decide⟩) =
    some ⟨[7, 11, 13], by decide⟩ := by decide

-- Whole-layout width matters even when each component separately fits.
example : ¬ (1 + 255 * word.encoding.words < 2 ^ 8) := by decide

private def input : State 8 := nested.initial (7, (11, 13))
private def first := firstRealizer .unit (by decide) word pair (by decide) (by decide)
private def second := secondRealizer .unit (by decide) word pair (by decide) (by decide)

-- Multiword projections really copy through scratch and release it. The peak
-- includes the scratch allocation while the original input is still resident.
example : (Caliper.run .unit RandomTape.zero 100 first.code input).map
    (fun (state, time, net, peak) =>
      (state.bufs 0, state.caps 1, state.regs 0, time, net, peak)) =
    some (#[7], 0, 0, 8, -2, 1) := by decide
example : (Caliper.run .unit RandomTape.zero 100 second.code input).map
    (fun (state, time, net, peak) =>
      (state.bufs 0, state.caps 1, state.regs 0, time, net, peak)) =
    some (#[11, 13], 0, 0, 16, -1, 2) := by decide
example : descriptionWords second.code = 66 := by decide
example : (Caliper.run .unit RandomTape.zero 100 (selectSlice 2 2) input).isNone = true := by decide

private def lengthCode := listLengthRealizer .unit (by decide) word 3 (by decide) (by decide) (by decide)
example : (Caliper.run .unit RandomTape.zero 100 lengthCode.code
    (list.initial ⟨[7, 11], by decide⟩)).map (fun (state, time, _, _) => (state.bufs 0, time)) =
    some (#[2], 8) := by decide

private def tape : RandomTape 8 := fun index => BitVec.ofNat 8 (7 + 2 * index)
private def replayCode : Stmt 8 :=
  .memAllocI 0 4 ;; .imm 0 0 ;;
  Replay.read ;; Replay.read ;; Replay.read ;; Replay.rewind ;;
  Replay.read ;; Replay.read ;; Replay.read

-- Three fresh samples and three replayed samples consume only three physical
-- tape words. The cache allocation and cursor reset are included in the cost.
example : (Caliper.run .unit tape 200 replayCode (State.init 8)).map
    (fun (state, time, net, peak) =>
      ((state.bufs 0, state.regs 0, state.regs 1), (state.tapePos, time), (net, peak))) =
    some ((#[7, 9, 11], 3, 11), (3, 45), (4, 4)) := by decide

private def full : State 8 :=
  { State.init 8 with
    bufs := fun buffer => if buffer = 0 then #[7] else #[]
    caps := fun buffer => if buffer = 0 then 1 else 0
    tapePos := 1 }
example : (Caliper.run .unit tape 40 Replay.read full).map
    (fun (state, time, _, _) => (state.regs 1, state.tapePos, time)) = some (7, 1, 6) := by decide
example : (Caliper.run .unit tape 40 Replay.read (full.setReg 0 1)).isNone = true := by decide

-- Request transfer leaves a private buffer/register and the physical tape
-- untouched, charges all three words, and restores the zero-offset ABI.
private def caller : State 8 :=
  { input with
    regs := fun register => if register = 9 then 99 else 0
    bufs := fun buffer => if buffer = 2 then #[42] else input.bufs buffer
    caps := fun buffer => if buffer = 2 then 1 else input.caps buffer
    tapePos := 7 }
example : (Caliper.run .unit tape 100 (Mailbox.transfer 0 1) caller).map
    (fun (state, time, net, peak) =>
      ((state.bufs 1, state.bufs 2), (state.regs 9, state.regs 0), (state.tapePos, time), (net, peak))) =
    some ((#[7, 11, 13], #[42]), (99, 0), (7, 26), (3, 3)) := by decide

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Encoding.fin, ``Encoding.prod, ``Encoding.sum, ``Encoding.boundedList,
      ``copySlice_exec, ``selectSlice_exec, ``firstRealizer, ``secondRealizer,
      ``listLengthRealizer, ``Replay.read_exec, ``Replay.read_refines,
      ``Replay.read_frame, ``Replay.rewind_exec, ``Replay.rewind_recorded,
      ``Mailbox.transfer_spec, ``Mailbox.transfer_frame] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperIntegration
