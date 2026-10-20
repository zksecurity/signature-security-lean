import Signatures.Runtime.Caliper.SchnorrROMSigningSource
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMSigning

-- Modular words exercise the actual instructions; the source theorem is
-- separately polymorphic over the field and group used by the security game.
private instance : SMul (Word 16) (Word 16) := ⟨fun scalar point => scalar * point⟩
private def layout : SchnorrROM.Signing.Layouts 16 Nat (Word 16) (Word 16) where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  capacityPred := 2
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def scale : Implementation .unit layout.arithmetic.scaleArgs layout.point (fun input => input.1 • input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput layout.arithmetic.scaleArgs.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput layout.point.representation
      (fun input => ⟨input.val.1 * input.val.2, trivial⟩) (fun _ => rfl)
private def sub : Implementation .unit layout.arithmetic.points layout.point (fun input => input.1 - input.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .sub (by decide)).viewInput layout.arithmetic.points.representation
    (fun input => input.val) (fun _ => rfl)).viewOutput layout.point.representation
      (fun input => ⟨input.val.1 - input.val.2, trivial⟩) (fun _ => rfl)
private theorem scaleBound : scale.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem scaleNames : NamesBound scale.program.code 3 := ⟨by decide, by decide⟩
private theorem subNames : NamesBound sub.program.code 3 := ⟨by decide, by decide⟩

open SchnorrROM.Signing.Core
private def program := implementation layout trivial scale sub scaleNames.buffers subNames.buffers (by decide)
private theorem bounded : program.BoundedBy (timeBudget layout 6 6) (codeBudget layout 27 27) :=
  SchnorrROM.Signing.Core.bounded layout trivial scale sub scaleNames.buffers subNames.buffers (by decide) scaleBound subBound
private theorem named : NamesAccounted program.program.code 5 :=
  names layout trivial scale sub scaleNames.buffers subNames.buffers (by decide) 3 scaleNames.accounted subNames.accounted
private theorem bufferBound : program.program.code.memBound ≤ 9 :=
  buffers layout trivial scale sub scaleNames.buffers subNames.buffers (by decide)
private theorem accepted : DescriptionFits program.program.code := program.program.description_fits

private theorem valid_iff (c s g pk : Word 16) (message : Nat) (entries : List ((Nat × Word 16) × Word 16)) :
    layout.input.valid ((c, s), g, pk, message, entries) ↔
      (message < 256 ∧ entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧ entries.length ≤ 2 := by
  change (((True ∧ True) ∧ True ∧ True ∧ message < 256 ∧
    entries.length ≤ 3 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ True) ∧ entries.length ≤ 2) ↔ _
  simp only [true_and, and_true]

private def initial : layout.input.Value :=
  ⟨((2, 11), 3, 5, 7, [((5, 6), 1)]), by rw [valid_iff]; decide⟩
private def changed : layout.input.Value :=
  ⟨((3, 19), 2, 7, 8, []), by rw [valid_iff]; decide⟩
private def cachedZero : layout.input.Value :=
  ⟨((2, 11), 3, 5, 7, [((7, 23), 0), ((7, 23), 9)]), by rw [valid_iff]; decide⟩
private def fillsTable : layout.input.Value :=
  ⟨((65535, 2), 5, 3, 255, [((3, 4), 2), ((5, 6), 1)]), by rw [valid_iff]; decide⟩
private def zeroScalars : layout.input.Value :=
  ⟨((0, 0), 5, 3, 0, []), by rw [valid_iff]; decide⟩

example : ¬ layout.input.valid ((0, 0), 1, 1, 256, []) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ((0, 0), 1, 1, 0, [((256, 0), 1)]) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ((0, 0), 1, 1, 0, List.replicate 3 ((0, 0), 0)) := by rw [valid_iff]; decide

private def execute (input : layout.input.Value) :=
  let initial := layout.input.representation.initial input
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 1000000 program.program.code before).map fun result =>
    (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 30).all (fun i => result.1.caps (i + 1) == 0), decide (result.2.1 ≤ timeBudget layout 6 6))

open Lean in
run_cmd do
  unless execute initial == some (#[23, 11, 3, 5, 2, 7, 23, 2, 5, 6, 1, 0, 0, 0], #[77], 4, 91, 9, true, true) do
    throwError "signing lost its computed commitment, response, configuration, cache insertion or frame"
  unless execute changed == some (#[17, 19, 2, 7, 1, 8, 17, 3, 0, 0, 0, 0, 0, 0], #[77], 4, 91, 9, true, true) do
    throwError "signing ignored changed runtime scalars, points or message"
  unless execute cachedZero == some (#[23, 11, 3, 5, 2, 7, 23, 0, 7, 23, 9, 0, 0, 0], #[77], 4, 91, 9, true, true) do
    throwError "signing overwrote a cached zero or changed duplicate entries"
  unless execute fillsTable == some (#[13, 2, 5, 3, 3, 255, 13, 65535, 3, 4, 2, 5, 6, 1], #[77], 4, 91, 9, true, true) do
    throwError "signing lost word wraparound or its final reserved insertion slot"
  unless execute zeroScalars == some (#[0, 0, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[77], 4, 91, 9, true, true) do
    throwError "signing rejected zero scalars or failed to store a zero challenge"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``SchnorrROM.Signing.Arithmetic.arguments, ``SchnorrROM.Signing.Arithmetic.finish,
      ``SchnorrROM.Signing.Arithmetic.implementation, ``SchnorrROM.Signing.Arithmetic.bounded,
      ``SchnorrROM.Signing.Cache.implementation, ``SchnorrROM.Signing.Cache.bounded,
      ``SchnorrROM.Signing.Core.implementation, ``SchnorrROM.Signing.Core.bounded,
      ``SchnorrROM.Signing.Core.resources, ``SchnorrROM.Signing.Core.value_original,
      ``SchnorrROM.Signing.signing_run, ``bounded, ``named, ``bufferBound, ``accepted] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMSigning
