import Signatures.Runtime.Caliper.CoronResponseMemory
import Lean

/-! Exercise both Coron branches with distinct encoded challenge points and
ordinary word arithmetic primitives. Field/module source equality remains the
separate generic theorem; these runs test wiring, zero tests and resource bounds. -/
namespace SignaturesTest.CaliperCoronResponse
open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

private def layout : CoronResponse.Layouts 8 (Word 8) (Word 8) 255 where
  scalar := Layout.all (wordRepresentation 8 (by decide))
  point := Layout.all (wordRepresentation 8 (by decide))
  wordFits := by decide
  coinFits := by decide
  storageFits := by decide

private def binary (op : BinOp) : Implementation .unit layout.scaleArgs layout.point
    (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op layout.wordFits).viewInput layout.scaleArgs.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.point.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)
private def scale : Implementation .unit layout.scaleArgs layout.point (fun value => value.1 • value.2) := binary .mul
private def add : Implementation .unit layout.points layout.point (fun value => value.1 + value.2) := binary .add
private theorem scale_bound : scale.BoundedBy 6 27 := ⟨fun _ => le_rfl, le_rfl⟩
private theorem add_bound : add.BoundedBy 6 27 := ⟨fun _ => le_rfl, le_rfl⟩
private theorem scale_names : NamesBound scale.program.code 3 := by constructor <;> decide
private theorem add_names : NamesBound add.program.code 3 := by constructor <;> decide
private theorem reserve : 3 + 3 < 2 ^ 8 := by decide
private def response := CoronResponse.reply layout trivial scale add scale_names.buffers reserve

example : (response false).BoundedBy 2000 7257 :=
  CoronResponse.reply_bounded layout trivial scale scale_bound scale_names.buffers reserve add add_bound false
example : (response true).BoundedBy 1354 4981 :=
  CoronResponse.reply_bounded layout trivial scale scale_bound scale_names.buffers reserve add add_bound true
example (signing : Bool) : (response signing).program.code.memBound ≤ 4 :=
  CoronResponse.reply_buffers layout trivial scale scale_names.buffers reserve add add_names.buffers signing
example (signing : Bool) : DescriptionFits (response signing).program.code := (response signing).program.description_fits
example (signing : Bool) : NamesAccounted (response signing).program.code 3 :=
  CoronResponse.reply_names layout 3 trivial scale scale_names.accounted scale_names.buffers reserve add add_names.accounted signing

private def input (scalar : Word 8) (coin : Fin 256) : layout.input.Value := ⟨((scalar, coin), 7, 11, 17), by trivial⟩
private def execute (signing : Bool) (scalar : Word 8) (coin : Fin 256) :=
  let value := input scalar coin
  let initial := layout.input.representation.initial value
  let before := { initial with
    regs := fun register => if register = 200 then 99 else initial.regs register
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 3 else initial.caps buffer
    tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 10000 (response signing).program.code before).map
    (fun (after, time, _, _) => (after.bufs 0, after.bufs 200, after.caps 200, after.regs 200, after.tapePos,
      decide (time ≤ CoronResponse.timeBudget layout signing 6 6)))

private def testZero (range : Nat) (fits : range + 1 ≤ 2 ^ 8) (value : Fin (range + 1)) :=
  let test := Finite.isZero range (by decide : 16 < 2 ^ 8) fits
  let before := (Finite.layout range (by decide : 16 < 2 ^ 8) fits).representation.initial ⟨value, trivial⟩
  (Caliper.run .unit RandomTape.zero 10 test.program.code before).map
    (fun (after, time, _, _) => (after.bufs 0, time))

open Lean in
run_cmd do
  unless execute false 3 0 == some (#[38], #[77], 3, 99, 9, true) do
    throwError "zero-coin hash did not add the challenge point"
  unless execute false 3 255 == some (#[21], #[77], 3, 99, 9, true) do
    throwError "maximal nonzero coin was misclassified or hash arguments were swapped"
  unless execute true 3 0 == some (#[0], #[77], 3, 99, 9, true) do
    throwError "zero-coin signing branch did not return the represented zero"
  unless execute true 3 255 == some (#[33], #[77], 3, 99, 9, true) do
    throwError "ordinary signing branch did not scale the key point"
  unless execute false 0 0 == some (#[17], #[77], 3, 99, 9, true) do
    throwError "zero scalar lost the hash challenge offset"
  unless execute true 0 1 == some (#[0], #[77], 3, 99, 9, true) do
    throwError "nonzero coin with zero scalar returned a nonzero signature"
  unless testZero 0 (by decide) 0 == some (#[1], 5) do
    throwError "singleton finite-domain zero test failed"
  unless testZero 255 (by decide) 255 == some (#[0], 5) do
    throwError "full-word finite-domain zero test failed"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Finite.word_zero, ``Finite.isZero, ``Finite.isZero_bounded, ``Finite.isZero_names,
      ``CoronResponse.reply, ``CoronResponse.zero_valid, ``CoronResponse.reply_source, ``CoronResponse.reply_bounded,
      ``CoronResponse.reply_names, ``CoronResponse.reply_buffers, ``CoronResponse.reply_memoryBound,
      ``scale_bound, ``add_bound] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperCoronResponse
