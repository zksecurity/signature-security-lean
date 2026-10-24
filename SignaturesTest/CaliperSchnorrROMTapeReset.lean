import Proofs.Runtime.Caliper.SchnorrROMTapeResetBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperSchnorrROMTapeReset

private def layout : SchnorrROMTape.Layouts 12 Nat where
  scalar := Layout.counter 12 4096 (by decide) (by decide)
  capacity := 6
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def emptyLayout : SchnorrROMTape.Layouts 12 Nat :=
  { layout with capacity := 0, countFits := by decide, storageFits := by decide }

-- Two private uniform families are interleaved with challenge replies. Their
-- suffixes must survive resetting any challenge slot, including slot zero.
private def saved : List (Schnorr.TapeCell Nat) :=
  [(3, 0, 5), (1, 11, 0), (7, 0, 2), (1, 22, 0), (3, 0, 8), (1, 33, 0)]
private theorem saved_valid : (layout.list layout.capacity (by omega)).valid saved := by
  change 6 ≤ 6 ∧ ∀ value ∈ [(3, 0, 5), (1, 11, 0), (7, 0, 2), (1, 22, 0), (3, 0, 8), (1, 33, 0)],
    value.1 < 4096 ∧ value.2.1 < 4096 ∧ value.2.2 < 4096
  simp
private def input (slot : Fin 4096) (answer : Fin 4096) : layout.resetInput.Value :=
  ⟨(slot.val, (1, answer.val, 0), saved), slot.isLt, ⟨by change 1 < 4096; decide, answer.isLt, by change 0 < 4096; decide⟩, saved_valid⟩
private def noCells : emptyLayout.resetInput.Value :=
  ⟨(0, (1, 0, 0), []), by
    change 0 < 4096 ∧ (1 < 4096 ∧ 0 < 4096 ∧ 0 < 4096) ∧ 0 ≤ 0 ∧
      ∀ value ∈ ([] : List (Schnorr.TapeCell Nat)), emptyLayout.entry.valid value
    simp⟩
private def shortInput : layout.resetInput.Value :=
  ⟨(0, (1, 7, 0), [(3, 0, 5), (1, 11, 0)]), by
    change 0 < 4096 ∧ (1 < 4096 ∧ 7 < 4096 ∧ 0 < 4096) ∧ 2 ≤ 6 ∧
      ∀ value ∈ [(3, 0, 5), (1, 11, 0)], value.1 < 4096 ∧ value.2.1 < 4096 ∧ value.2.2 < 4096
    simp⟩

example : ¬ layout.resetInput.valid (4096, (1, 0, 0), []) := by
  intro valid
  have impossible : 4096 < 4096 := valid.1
  omega
example : ¬ layout.resetInput.valid (0, (1, 4096, 0), []) := by
  intro valid
  have impossible : 4096 < 4096 := valid.2.1.2.1
  omega
example : ¬ layout.resetInput.valid (0, (1, 0, 0), saved ++ [(1, 44, 0)]) := by
  intro valid
  have impossible : 7 ≤ 6 := valid.2.2.1
  omega
example : ¬ layout.resetInput.valid (0, (1, 0, 0), [(4096, 0, 0)]) := by
  intro valid
  have impossible : 4096 < 4096 := (valid.2.2.2 (4096, 0, 0) (by simp)).1
  omega

example (slot answer : Nat) (state : Schnorr.RawTape.State Nat) :
    Schnorr.LazySeed.State.fromTape (Schnorr.SeedTape.reset 1 slot (1, answer, 0) state.saved) =
      Schnorr.RawTape.restart slot answer state := SchnorrROMTape.source slot answer state
example : (SchnorrROMTape.implementation layout).program.code.memBound ≤ 6 := SchnorrROMTape.buffers layout
example : NamesAccounted (SchnorrROMTape.implementation layout).program.code 0 := SchnorrROMTape.names layout 0
example : DescriptionFits (SchnorrROMTape.implementation layout).program.code :=
  (SchnorrROMTape.implementation layout).program.description_fits
private theorem bounded : (SchnorrROMTape.implementation layout).BoundedBy
    (SchnorrROMTape.timeBudget layout) (SchnorrROMTape.codeBudget layout) := SchnorrROMTape.bounded layout

private def run (parameters : SchnorrROMTape.Layouts 12 Nat) (value : parameters.resetInput.Value) :=
  let initial := parameters.resetInput.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 100000 (SchnorrROMTape.implementation parameters).program.code before).map fun result =>
    ((parameters.replay.representation.encoding.decode (result.1.bufs 0).toList).map fun out =>
      (out.val.saved, out.val.remaining),
      result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 10).all (fun i => result.1.caps (i + 1) == 0))

open Lean in
run_cmd do
  let zero := [(3, 0, 5), (7, 0, 2), (3, 0, 8), (1, 99, 0)]
  let first := [(3, 0, 5), (1, 11, 0), (7, 0, 2), (3, 0, 8), (1, 99, 0)]
  let second := [(3, 0, 5), (1, 11, 0), (7, 0, 2), (1, 22, 0), (3, 0, 8), (1, 99, 0)]
  let all := saved ++ [(1, 99, 0)]
  for (slot, expected) in [((0 : Fin 4096), zero), (1, first), (2, second), (3, all), (4095, all)] do
    unless run layout (input slot 99) == some (some (expected, expected), #[77], 4, 91, 9, true) do
      throwError "Caliper replay reset changed the wrong family or failed to restore both tapes at slot {slot.val}"
  let zeroAnswer := [(3, 0, 5), (7, 0, 2), (3, 0, 8), (1, 0, 0)]
  unless run layout (input 0 0) == some (some (zeroAnswer, zeroAnswer), #[77], 4, 91, 9, true) do
    throwError "zero is a valid replacement challenge"
  unless run emptyLayout noCells == some (some ([(1, 0, 0)], [(1, 0, 0)]), #[77], 4, 91, 9, true) do
    throwError "zero-capacity reset did not insert the new challenge"
  let shortExpected := [(3, 0, 5), (1, 7, 0)]
  unless run layout shortInput == some (some (shortExpected, shortExpected), #[77], 4, 91, 9, true) do
    throwError "early-return padding changed the replay tape"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``SchnorrROMTape.body, ``SchnorrROMTape.body_accepted, ``SchnorrROMTape.body_bounded,
      ``SchnorrROMTape.loop, ``SchnorrROMTape.accepted, ``SchnorrROMTape.loop_source,
      ``SchnorrROMTape.implementation, ``SchnorrROMTape.source, ``SchnorrROMTape.bounded,
      ``SchnorrROMTape.names, ``SchnorrROMTape.resources, ``SchnorrROMTape.restart_resources, ``bounded] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMTapeReset
