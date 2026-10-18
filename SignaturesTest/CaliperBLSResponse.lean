import Signatures.Runtime.Caliper.BLSResponseMemory
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource

namespace SignaturesTest.CaliperBLSResponse

-- Word arithmetic exercises the generated wiring with executable primitives.
-- The source-agreement theorems themselves quantify over fields and modules.
private def layout : BLSResponse.Layouts 8 (Word 8) (Word 8) where
  scalar := Layout.all (wordRepresentation 8 (by decide))
  point := Layout.all (wordRepresentation 8 (by decide))
  wordFits := by decide
  storageFits := by decide

private def binary (op : BinOp) : Implementation .unit layout.scaleArgs layout.point
    (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op layout.wordFits).viewInput layout.scaleArgs.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.point.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)

private def scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2) := binary .mul
private def add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2) := binary .add

private theorem scale_bound : scale.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem add_bound : add.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem scale_names : NamesBound scale.program.code 3 := by constructor <;> decide
private theorem add_names : NamesBound add.program.code 3 := by constructor <;> decide
private theorem reserve : 3 + 3 < 2 ^ 8 := by decide

private def good := BLSResponse.good layout scale
private def bad := BLSResponse.bad layout scale add scale_names.buffers reserve add_names.buffers

example (signing : Bool) : (good signing).BoundedBy 246 975 := BLSResponse.good_bounded layout scale scale_bound signing
example : (bad false).BoundedBy 1098 4112 :=
  BLSResponse.bad_bounded layout scale add scale_bound add_bound scale_names.buffers reserve add_names.buffers false
example : (bad true).BoundedBy 1448 5411 :=
  BLSResponse.bad_bounded layout scale add scale_bound add_bound scale_names.buffers reserve add_names.buffers true
example (signing : Bool) : DescriptionFits (bad signing).program.code := (bad signing).program.description_fits
example (signing : Bool) : (good signing).program.code.memBound ≤ 3 := BLSResponse.good_buffers layout scale scale_names.buffers signing
example (signing : Bool) : (bad signing).program.code.memBound ≤ 5 :=
  BLSResponse.bad_buffers layout scale add scale_names.buffers reserve add_names.buffers signing
example (signing : Bool) : staticWords (good signing).program.code 201 201 ≤ 5691 :=
  (BLSResponse.good_bounded layout scale scale_bound signing).staticMemory
    (BLSResponse.good_names layout 3 scale scale_names.accounted signing) 201 201

private def observe {A : Type} {input : Layout 8 A} {f : A → Word 8}
    (implementation : Implementation .unit input layout.point f) (value : input.Value) :=
  let initial := input.representation.initial value
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 3 else initial.caps buffer
    tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 6000 implementation.program.code before).map
    (fun (state, _, _, _) => (state.bufs 0, state.bufs 200, state.caps 200, state.regs 200, state.tapePos))

private def goodInput : layout.config.Value := ⟨(3, 7, 11), by trivial⟩
private def badInput : layout.badInput.Value := ⟨((2, 3), 5, 7, 11), by trivial⟩
private def zeroMask : layout.badInput.Value := ⟨((0, 3), 5, 7, 11), by trivial⟩

-- Distinct masks and points detect swapped arguments and lost retained input.
-- Spare caller capacity, filled contents, a high register and tape position survive.
example : observe (good false) goodInput = some (#[21], #[77], 3, 99, 9) := by decide +kernel
example : observe (good true) goodInput = some (#[33], #[77], 3, 99, 9) := by decide +kernel
example : observe (bad false) badInput = some (#[43], #[77], 3, 99, 9) := by decide +kernel
example : observe (bad true) badInput = some (#[215], #[77], 3, 99, 9) := by decide +kernel
example : observe (bad false) zeroMask = some (#[21], #[77], 3, 99, 9) := by decide +kernel

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``BLSResponse.good_source, ``BLSResponse.bad_source, ``BLSResponse.good_bounded, ``BLSResponse.bad_bounded,
      ``BLSResponse.good_names, ``BLSResponse.bad_names, ``BLSResponse.good_buffers, ``BLSResponse.bad_buffers,
      ``Implementation.BoundedBy.staticMemory, ``Implementation.BoundedBy.memoryBound,
      ``BLSResponse.good_memoryBound, ``BLSResponse.bad_memoryBound, ``scale_bound, ``add_bound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperBLSResponse
