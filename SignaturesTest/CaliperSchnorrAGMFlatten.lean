import Signatures.Runtime.Caliper.SchnorrAGMFlattenBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMFlatten

-- Word arithmetic is an executable wiring fixture. The generic source theorem
-- separately connects field arithmetic to Schnorr's original affine flattening.
private def layout : CaliperBackend.SchnorrAGM.Flatten.Layouts 16 (Word 16) where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  capacity := 3
  coefficients := 5
  wordFits := by decide
  counterFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide

private def mul : Implementation .unit layout.affine layout.scalar (fun value => value.1 * value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput layout.affine.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.scalar.representation
      (fun value => ⟨value.val.1 * value.val.2, trivial⟩) (fun _ => rfl)
private def add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .add (by decide)).viewInput layout.affine.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.scalar.representation
      (fun value => ⟨value.val.1 + value.val.2, trivial⟩) (fun _ => rfl)
private theorem mulBound : mul.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem addBound : add.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem mulNames : NamesBound mul.program.code 3 := ⟨by decide, by decide⟩
private theorem addNames : NamesBound add.program.code 3 := ⟨by decide, by decide⟩
private def program := CaliperBackend.SchnorrAGM.Flatten.implementation layout trivial mul add mulNames.buffers addNames.buffers (by decide)

private theorem bounded : program.BoundedBy (CaliperBackend.SchnorrAGM.Flatten.timeBudget layout 6 6)
    (CaliperBackend.SchnorrAGM.Flatten.codeBudget layout 27 27) :=
  CaliperBackend.SchnorrAGM.Flatten.bounded layout trivial mul add mulNames.buffers addNames.buffers (by decide) mulBound addBound
private theorem names : NamesAccounted program.program.code 3 :=
  CaliperBackend.SchnorrAGM.Flatten.names layout trivial mul add mulNames.buffers addNames.buffers (by decide) 3 mulNames.accounted addNames.accounted
private theorem buffers : program.program.code.memBound ≤ 10 :=
  CaliperBackend.SchnorrAGM.Flatten.buffers layout trivial mul add mulNames.buffers addNames.buffers (by decide)
private theorem accepted : DescriptionFits program.program.code := program.program.description_fits

private theorem valid_iff (basis : List (Word 16 × Word 16)) (coefficients : List (Word 16)) :
    layout.input.valid (basis, coefficients) ↔ basis.length ≤ 3 ∧ coefficients.length ≤ 5 := by
  change ((basis.length ≤ 3 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (coefficients.length ≤ 5 ∧ ∀ coefficient ∈ coefficients, True)) ↔ _
  simp only [implies_true, and_true]

private def input (basis : List (Word 16 × Word 16)) (coefficients : List (Word 16))
    (fits : basis.length ≤ 3 ∧ coefficients.length ≤ 5) : layout.input.Value :=
  ⟨(basis, coefficients), (valid_iff basis coefficients).mpr fits⟩

example : ¬ layout.input.valid (List.replicate 4 (0, 0), []) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([], List.replicate 6 0) := by rw [valid_iff]; decide

private theorem memory (tape : RandomTape 16) (value : layout.input.Value) (before : State 16)
    (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape program.program.code before after (program.program.time value) net peak ∧
      layout.affine.representation.Holds ⟨CaliperBackend.SchnorrAGM.Flatten.denote value.val, program.preserves value.val value.property⟩ after ∧
      program.program.time value ≤ CaliperBackend.SchnorrAGM.Flatten.timeBudget layout 6 6 ∧
      ∀ between, (Caliper.Reaches .unit tape program.program.code before between ∨ between = after) →
        (staticWords program.program.code registers buffers : Int) + between.liveMem (max buffers program.program.code.memBound) ≤
          5 * CaliperBackend.SchnorrAGM.Flatten.codeBudget layout 27 27 + 12 + registers + 3 * buffers + before.liveMem buffers +
            CaliperBackend.SchnorrAGM.Flatten.timeBudget layout 6 6 :=
  CaliperBackend.SchnorrAGM.Flatten.resources layout trivial mul add mulNames.buffers addNames.buffers (by decide)
    mulBound addBound mulNames.accounted addNames.accounted tape value before holds registers buffers initialRegisters initialBuffers

private def execute (value : layout.input.Value) :=
  let initial := layout.input.representation.initial value
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 1000000 program.program.code before).map fun result =>
    (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 30).all (fun i => result.1.caps (i + 1) == 0),
      decide (result.2.1 ≤ CaliperBackend.SchnorrAGM.Flatten.timeBudget layout 6 6))

open Lean in
run_cmd do
  unless execute (input [(1, 0), (0, 1), (5, 7)] [2, 3, 4] (by decide)) ==
      some (#[22, 31], #[77], 4, 91, 9, true, true) do
    throwError "affine fold lost coordinate arithmetic, chronology, framing, scratch release or time bounds"
  unless execute (input [(1, 0), (0, 1), (5, 7)] [2] (by decide)) ==
      some (#[2, 0], #[77], 4, 91, 9, true, true) do
    throwError "missing coefficients did not receive the stored zero default"
  unless execute (input [(1, 0), (0, 1), (5, 7)] [2, 3, 4, 99, 100] (by decide)) ==
      some (#[22, 31], #[77], 4, 91, 9, true, true) do
    throwError "surplus coefficients created extra basis entries or changed the affine result"
  unless execute (input [(1, 0), (0, 1), (5, 7)] [] (by decide)) ==
      some (#[0, 0], #[77], 4, 91, 9, true, true) do
    throwError "an empty coefficient list did not flatten to zero"
  unless execute (input [] [2, 3, 4, 99, 100] (by decide)) ==
      some (#[0, 0], #[77], 4, 91, 9, true, true) do
    throwError "empty basis did not stop the fold and preserve the zero accumulator"
  unless execute (input [(5, 7), (0, 1), (1, 0)] [2, 3, 4] (by decide)) ==
      some (#[14, 17], #[77], 4, 91, 9, true, true) do
    throwError "flattening ignored runtime basis order"
  unless execute (input [(5, 7), (1, 1)] [65535, 2] (by decide)) ==
      some (#[65533, 65531], #[77], 4, 91, 9, true, true) do
    throwError "flattening failed to execute the supplied modular scalar operations"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CaliperBackend.SchnorrAGM.Flatten.route, ``CaliperBackend.SchnorrAGM.Flatten.body,
      ``CaliperBackend.SchnorrAGM.Flatten.prepare, ``CaliperBackend.SchnorrAGM.Flatten.initial,
      ``CaliperBackend.SchnorrAGM.Flatten.implementation, ``CaliperBackend.SchnorrAGM.Flatten.denote_value,
      ``CaliperBackend.SchnorrAGM.Flatten.denote_source, ``CaliperBackend.SchnorrAGM.Flatten.bounded,
      ``CaliperBackend.SchnorrAGM.Flatten.names, ``CaliperBackend.SchnorrAGM.Flatten.buffers,
      ``CaliperBackend.SchnorrAGM.Flatten.resources, ``bounded, ``names, ``buffers, ``accepted, ``memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMFlatten
