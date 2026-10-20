import Signatures.Runtime.Caliper.SchnorrROMTapeRestart
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMTapeRestart
open SchnorrROMTape

private def layout : Layouts 12 Nat where
  scalar := Layout.counter 12 4096 (by decide) (by decide)
  capacity := 6
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def emptyLayout : Layouts 12 Nat :=
  { layout with capacity := 0, countFits := by decide, storageFits := by decide }
private def saved : List (Schnorr.TapeCell Nat) :=
  [(3, 0, 1), (1, 11, 0), (7, 0, 2), (1, 22, 0), (3, 0, 0), (1, 33, 0)]
private def oldState : Schnorr.RawTape.State Nat :=
  ⟨saved, [(9, 0, 7), (1, 77, 0)]⟩
private theorem saved_valid : (Read.list layout).valid saved := by
  change 6 ≤ 6 ∧ ∀ cell ∈ saved, cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096
  simp [saved]
private def input (slot answer : Fin 4096) : (Restart.input layout).Value :=
  ⟨Restart.rawInput slot.val answer.val oldState, slot.isLt, answer.isLt, saved_valid, by
    change 2 ≤ 6 ∧ ∀ cell ∈ [(9, 0, 7), (1, 77, 0)], cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096
    simp⟩
private def empty : (Restart.input emptyLayout).Value :=
  ⟨Restart.rawInput 0 0 {}, by
    change 0 < 4096 ∧ 0 < 4096 ∧
      (0 ≤ 0 ∧ ∀ cell ∈ ([] : List (Schnorr.TapeCell Nat)), emptyLayout.entry.valid cell) ∧
      (0 ≤ 0 ∧ ∀ cell ∈ ([] : List (Schnorr.TapeCell Nat)), emptyLayout.entry.valid cell)
    simp⟩

example : ¬ (Restart.input layout).valid (Restart.rawInput 4096 0 oldState) := by
  intro valid
  have impossible : 4096 < 4096 := valid.1
  omega
example : ¬ (Restart.input layout).valid (Restart.rawInput 0 4096 oldState) := by
  intro valid
  have impossible : 4096 < 4096 := valid.2.1
  omega
example : ¬ (Restart.input layout).valid (Restart.rawInput 0 0 ⟨[], saved ++ [(1, 44, 0)]⟩) := by
  intro valid
  have impossible : 7 ≤ 6 := valid.2.2.2.1
  omega

example : (Restart.implementation layout).program.code.memBound ≤ 6 := Restart.buffers layout
example : DescriptionFits (Restart.implementation layout).program.code :=
  (Restart.implementation layout).program.description_fits
private theorem bounded : (Restart.implementation layout).BoundedBy
    (Restart.timeBudget layout) (Restart.codeBudget layout) := Restart.bounded layout

private def run (parameters : Layouts 12 Nat) (value : (Restart.input parameters).Value) :=
  let initial := (Restart.input parameters).representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 100000 (Restart.implementation parameters).program.code before).map fun result =>
    ((parameters.replay.representation.encoding.decode (result.1.bufs 0).toList).map
      (fun out => (out.val.saved, out.val.remaining)),
      result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 10).all (fun i => result.1.caps (i + 1) == 0))

open Lean in
run_cmd do
  let zero := [(3, 0, 1), (7, 0, 2), (3, 0, 0), (1, 99, 0)]
  let first := [(3, 0, 1), (1, 11, 0), (7, 0, 2), (3, 0, 0), (1, 99, 0)]
  let all := saved ++ [(1, 99, 0)]
  for (slot, expected) in [((0 : Fin 4096), zero), (1, first), (4095, all)] do
    unless run layout (input slot 99) == some (some (expected, expected), #[77], 4, 91, 9, true) do
      throwError "complete restart lost saved cells, reused the old remaining tape, or damaged a caller frame at slot {slot.val}"
  let zeroAnswer := [(3, 0, 1), (7, 0, 2), (3, 0, 0), (1, 0, 0)]
  unless run layout (input 0 0) == some (some (zeroAnswer, zeroAnswer), #[77], 4, 91, 9, true) do
    throwError "restart packet construction lost a zero replacement scalar"
  unless run emptyLayout empty == some (some ([(1, 0, 0)], [(1, 0, 0)]), #[77], 4, 91, 9, true) do
    throwError "complete restart failed on an empty retained state"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Restart.prepare, ``Restart.prepare_budget, ``Restart.constructed,
      ``Restart.bounded, ``Restart.buffers, ``Restart.source_rawInput, ``Restart.resources, ``bounded] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMTapeRestart
