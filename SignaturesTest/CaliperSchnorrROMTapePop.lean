import Proofs.Runtime.Caliper.SchnorrROMTapePop
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMTapePop

private def layout : SchnorrROMTape.Layouts 12 Nat where
  scalar := Layout.counter 12 4096 (by decide) (by decide)
  capacity := 6
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def emptyLayout : SchnorrROMTape.Layouts 12 Nat :=
  { layout with capacity := 0, countFits := by decide, storageFits := by decide }
private def cells : List (Schnorr.TapeCell Nat) :=
  [(3, 0, 1), (1, 0, 0), (7, 0, 2), (1, 22, 0), (3, 0, 0), (1, 33, 0)]
private theorem cells_valid : (layout.list layout.capacity (by omega)).valid cells := by
  change 6 ≤ 6 ∧ ∀ cell ∈ cells, cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096
  simp [cells]
private def input (tag : Fin 4096) : layout.resetInput.Value :=
  ⟨(tag.val, (9, 88, 77), cells), tag.isLt,
    ⟨by change 9 < 4096; decide, by change 88 < 4096; decide, by change 77 < 4096; decide⟩, cells_valid⟩
private def empty : emptyLayout.resetInput.Value := ⟨(1, (9, 88, 77), []), by
  change 1 < 4096 ∧ (9 < 4096 ∧ 88 < 4096 ∧ 77 < 4096) ∧ 0 ≤ 0 ∧
    ∀ cell ∈ ([] : List (Schnorr.TapeCell Nat)), emptyLayout.entry.valid cell
  simp⟩

private def run (parameters : SchnorrROMTape.Layouts 12 Nat) (value : parameters.resetInput.Value) :=
  let initial := parameters.resetInput.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 100000 (SchnorrROMTape.Pop.implementation parameters).program.code before).map fun result =>
    ((SchnorrROMTape.Pop.state parameters parameters.capacity (by omega)).representation.encoding.decode
      (result.1.bufs 0).toList |>.map Subtype.val,
      result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 10).all (fun i => result.1.caps (i + 1) == 0))

example : (SchnorrROMTape.Pop.implementation layout).program.code.memBound ≤ 6 := SchnorrROMTape.Pop.buffers layout
example : NamesAccounted (SchnorrROMTape.Pop.implementation layout).program.code 0 := SchnorrROMTape.Pop.names layout 0
example : DescriptionFits (SchnorrROMTape.Pop.implementation layout).program.code :=
  (SchnorrROMTape.Pop.implementation layout).program.description_fits
private theorem bounded : (SchnorrROMTape.Pop.implementation layout).BoundedBy
    (SchnorrROMTape.Pop.timeBudget layout) (SchnorrROMTape.Pop.codeBudget layout) := SchnorrROMTape.Pop.bounded layout

open Lean in
run_cmd do
  let cases := [
    ((1 : Fin 4096), (true, (1, 0, 0), [(3, 0, 1), (7, 0, 2), (1, 22, 0), (3, 0, 0), (1, 33, 0)])),
    (3, (true, (3, 0, 1), [(1, 0, 0), (7, 0, 2), (1, 22, 0), (3, 0, 0), (1, 33, 0)])),
    (7, (true, (7, 0, 2), [(3, 0, 1), (1, 0, 0), (1, 22, 0), (3, 0, 0), (1, 33, 0)])),
    (4095, (false, (9, 88, 77), cells))]
  for (tag, expected) in cases do
    unless run layout (input tag) == some (some expected, #[77], 4, 91, 9, true) do
      throwError "replay pop changed the wrong cell, order or caller frame for tag {tag.val}"
  unless run emptyLayout empty == some (some (false, (9, 88, 77), []), #[77], 4, 91, 9, true) do
    throwError "empty replay pop did not return its runtime fallback"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Constructed.then, ``Constructed.pair, ``Constructed.branch,
      ``SchnorrROMTape.Pop.body, ``SchnorrROMTape.Pop.loop, ``SchnorrROMTape.Pop.constructed,
      ``SchnorrROMTape.Pop.bounded, ``SchnorrROMTape.Pop.names, ``SchnorrROMTape.Pop.resources, ``bounded] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMTapePop
