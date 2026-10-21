import Signatures.Runtime.Caliper.SchnorrROMReplayAdmission
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMReplayRestart
open SchnorrROMTape

private def layout : Layouts 12 Nat where
  scalar := Layout.counter 12 4096 (by decide) (by decide)
  capacity := 6
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def saved : List (Schnorr.TapeCell Nat) :=
  [(3, 0, 1), (1, 11, 0), (7, 0, 2), (1, 22, 0), (3, 0, 0)]
private def input (slot answer : Fin 4096) : (ReplayRestart.input layout).Value :=
  ⟨(slot.val, answer.val, saved, [(9, 0, 7)]), by
    change (slot.val < 4096 ∧ answer.val < 4096 ∧
      (saved.length ≤ 6 ∧ ∀ cell ∈ saved, cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096) ∧
      (1 ≤ 6 ∧ ∀ cell ∈ [(9, 0, 7)], cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096)) ∧ saved.length < 6
    simp [saved, slot.isLt, answer.isLt]⟩
private def empty : (ReplayRestart.input layout).Value :=
  ⟨(0, 0, [], []), by
    change (0 < 4096 ∧ 0 < 4096 ∧ (0 ≤ 6 ∧ ∀ cell ∈ ([] : List (Schnorr.TapeCell Nat)), layout.entry.valid cell) ∧
      (0 ≤ 6 ∧ ∀ cell ∈ ([] : List (Schnorr.TapeCell Nat)), layout.entry.valid cell)) ∧ 0 < 6
    simp⟩
example : ¬ (ReplayRestart.input layout).valid (0, 0, saved ++ [(1, 33, 0)], []) := by
  intro valid
  have impossible : 6 < 6 := valid.2
  omega
example : (ReplayRestart.implementation layout).BoundedBy (ReplayRestart.timeBudget layout) (ReplayRestart.codeBudget layout) :=
  ReplayRestart.bounded layout

private def run (value : (ReplayRestart.input layout).Value) :=
  let initial := (ReplayRestart.input layout).representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 100000 (ReplayRestart.implementation layout).program.code before).map fun result =>
    (((Read.tapes layout).representation.encoding.decode (result.1.bufs 0).toList).map Subtype.val,
      result.1.bufs 0 |>.size, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 10).all (fun i => result.1.caps (i + 1) == 0),
      decide ((ReplayRestart.implementation layout).program.time value ≤ ReplayRestart.timeBudget layout))

open Lean in
run_cmd do
  let zero := [(3, 0, 1), (7, 0, 2), (3, 0, 0), (1, 99, 0)]
  let first := [(3, 0, 1), (1, 11, 0), (7, 0, 2), (3, 0, 0), (1, 99, 0)]
  let all := saved ++ [(1, 99, 0)]
  for (slot, expected) in [((0 : Fin 4096), zero), (1, first), (4095, all)] do
    unless run (input slot 99) == some (some (expected, expected), 38, #[77], 4, 91, 9, true, true) do
      throwError "bounded restart lost entries, retained extra padding or damaged caller state at slot {slot.val}"
  let zeroAnswer := [(3, 0, 1), (7, 0, 2), (3, 0, 0), (1, 0, 0)]
  unless run (input 0 0) == some (some (zeroAnswer, zeroAnswer), 38, #[77], 4, 91, 9, true, true) do
    throwError "bounded restart lost a zero replacement scalar"
  unless run empty == some (some ([(1, 0, 0)], [(1, 0, 0)]), 38, #[77], 4, 91, 9, true, true) do
    throwError "bounded restart failed to install both tapes from an empty state"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ReplayRestart.parts_bytes, ``ReplayRestart.reset_fits, ``ReplayRestart.bounded,
      ``ReplayRestart.buffers, ``ReplayRestart.names, ``ReplayRestart.source_rawInput,
      ``SchnorrROM.Pass.Replay.first_ready, ``SchnorrROM.Pass.Replay.ready_empty,
      ``SchnorrROM.Pass.Replay.next_tapes, ``SchnorrROM.Pass.Replay.restart_room,
      ``SchnorrROM.Pass.Replay.second_ready, ``SchnorrROM.Pass.Replay.second_lengths] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMReplayRestart
