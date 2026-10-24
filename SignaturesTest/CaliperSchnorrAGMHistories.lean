import Proofs.Runtime.Caliper.SchnorrAGMHistoriesBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMHistories

private def scheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 2 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def layout : CaliperBackend.SchnorrAGM.Signing.Histories.Layouts 16 Nat (Word 16) (Word 16) 1 2 where
  signing := { scheme := scheme, storageFits := by decide }
  counterFits := by decide

open CaliperBackend.SchnorrAGM.Signing.Histories
private def program := implementation layout
private theorem budget : program.BoundedBy (timeBudget layout) (codeBudget layout) := bounded layout
private theorem named : NamesAccounted program.program.code 0 := names layout 0
private theorem bufferBound : program.program.code.memBound ≤ 8 := buffers layout
private theorem accepted : DescriptionFits program.program.code := program.program.description_fits

private theorem valid_iff (keyMessage message : Nat) (keyPoint c a b reply z x y : Word 16) (explained malformed bad : Bool)
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) :
    layout.input.valid (((keyMessage, keyPoint), (c, explained, a, b), entries, ()), (reply, z), (x, y), message, basis, signed, malformed, bad) ↔
      ((keyMessage < 256 ∧ (entries.length ≤ 4 ∧ ∀ entry ∈ entries, entry.1.1 < 256)) ∧
        message < 256 ∧ basis.length ≤ 4 ∧ (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256)) ∧
      basis.length < 4 ∧ signed.length < 2 := by
  change (((keyMessage < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True) ∧
    (entries.length ≤ 4 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧ True) ∧
    (True ∧ True) ∧ (True ∧ True) ∧ message < 256 ∧
    (basis.length ≤ 4 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧
      (basis.length < 4 ∧ signed.length < 2) ↔ _
  simp only [and_true, true_and, implies_true]

private def first : layout.input.Value :=
  ⟨(((7, 23), (2, false, 0, 0), [((5, 6), (1, true, 13, 14))], ()),
    (23, 11), (11, 65534), 7, [(1, 0), (0, 1)], [3], false, false), by rw [valid_iff]; decide⟩
private def full : layout.input.Value :=
  ⟨(((7, 31), (3, false, 0, 0),
    [((3, 4), (2, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14)), ((8, 9), (3, true, 15, 16))], ()),
    (31, 8), (8, 9), 7, [(1, 0), (0, 1), (5, 7)], [7], true, true), by rw [valid_iff]; decide⟩
private def empty : layout.input.Value :=
  ⟨(((0, 0), (0, false, 0, 0), [], ()), (0, 0), (0, 0), 0, [], [], true, false), by rw [valid_iff]; decide⟩
private def reordered : layout.input.Value :=
  ⟨(((9, 17), (5, true, 11, 12), [], ()), (42, 99), (0, 1), 9, [(5, 7), (1, 0)], [255], false, true), by rw [valid_iff]; decide⟩

example : ¬ layout.input.valid (((0, 0), (0, false, 0, 0), [], ()), (0, 0), (0, 0), 0,
    List.replicate 4 (0, 0), [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid (((0, 0), (0, false, 0, 0), [], ()), (0, 0), (0, 0), 0,
    [], [1, 2], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid (((256, 0), (0, false, 0, 0), [], ()), (0, 0), (0, 0), 0,
    [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid (((0, 0), (0, false, 0, 0), [], ()), (0, 0), (0, 0), 256,
    [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid (((0, 0), (0, false, 0, 0), [], ()), (0, 0), (0, 0), 0,
    [], [256], false, false) := by rw [valid_iff]; decide

private def zeroScheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 0 where
  scalar := scheme.scalar
  point := scheme.point
  message := scheme.message
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def zeroLayout : CaliperBackend.SchnorrAGM.Signing.Histories.Layouts 16 Nat (Word 16) (Word 16) 1 0 where
  signing := { scheme := zeroScheme, storageFits := by decide }
  counterFits := by decide
example (input : CaliperBackend.SchnorrAGM.Signing.Work Nat (Word 16) (Word 16)) : ¬ zeroLayout.input.valid input :=
  fun valid => Nat.not_lt_zero _ valid.2.2
private theorem zeroBudget : (implementation zeroLayout).BoundedBy (timeBudget zeroLayout) (codeBudget zeroLayout) := bounded zeroLayout

-- Zero-word entries still require an executed length increment and retain
-- their allocated header. No hidden positive-entry-width assumption is used.
private def units : ListSnoc.Layouts 16 Unit where
  entry := DataImplementation.unitLayout 16
  capacity := 2
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def unitInput : units.input.Value := ⟨((), [()]), ⟨trivial, by decide, by intro value member; trivial⟩, by decide⟩
private theorem unitsBudget : (ListSnoc.implementation units).BoundedBy (ListSnoc.timeBudget units) (ListSnoc.codeBudget units) :=
  ListSnoc.bounded units

private theorem memory (tape : RandomTape 16) (input : layout.input.Value) (before : State 16)
    (holds : layout.input.representation.Holds input before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape program.program.code before after (program.program.time input) net peak ∧
      layout.output.representation.Holds ⟨SchnorrAGM.Native.Signing.historiesValue input.val, program.preserves input.val input.property⟩ after ∧
      program.program.time input ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape program.program.code before between ∨ between = after) →
        (staticWords program.program.code registers buffers : Int) + between.liveMem (max buffers program.program.code.memBound) ≤
          5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout :=
  resources layout tape input before holds registers buffers initialRegisters initialBuffers

private def execute (input : layout.input.Value) :=
  let initial := layout.input.representation.initial input
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 1000000 program.program.code before).map fun result =>
    (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 30).all (fun i => result.1.caps (i + 1) == 0), decide (result.2.1 ≤ timeBudget layout))

open Lean in
run_cmd do
  let oneTable : Array (Word 16) := #[1, 5, 6, 1, 1, 13, 14] ++ Array.replicate 18 0
  let emptyTable : Array (Word 16) := Array.replicate 25 0
  unless execute first == some
      (#[7, 23, 2, 0, 0, 0] ++ oneTable ++ #[23, 11, 3, 1, 0, 0, 1, 11, 65534, 0, 0, 2, 3, 7, 0, 0],
        #[77], 4, 91, 9, true, true) do
    throwError "history update lost chronology, new entries, preserved cache/signature, framing, scratch release or time bound"
  unless execute full == some
      (#[7, 31, 3, 0, 0, 0, 4, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 0, 13, 14, 8, 9, 3, 1, 15, 16,
          31, 8, 4, 1, 0, 0, 1, 5, 7, 8, 9, 2, 7, 7, 1, 1], #[77], 4, 91, 9, true, true) do
    throwError "history update lost duplicate messages, full-cache entries, final-slot append or source flags"
  unless execute empty == some
      (#[0, 0, 0, 0, 0, 0] ++ emptyTable ++ #[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
        #[77], 4, 91, 9, true, true) do
    throwError "history update failed to append to empty histories or preserve malformed state"
  unless execute reordered == some
      (#[9, 17, 5, 1, 11, 12] ++ emptyTable ++ #[42, 99, 3, 5, 7, 1, 0, 0, 1, 0, 0, 2, 255, 9, 0, 1],
        #[77], 4, 91, 9, true, true) do
    throwError "history update changed runtime order, cached affine data, signature or bad flag"
  let unitResult := (Caliper.run .unit RandomTape.zero 1000000 (ListSnoc.implementation units).program.code
    (units.input.representation.initial unitInput)).map fun result =>
      (result.1.bufs 0, (List.range 10).all (fun i => result.1.caps (i + 1) == 0),
        decide (result.2.1 ≤ ListSnoc.timeBudget units))
  unless unitResult == some (#[2], true, true) do throwError "zero-word append lost the length header, scratch cleanup or time bound"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ListSnoc.implementation, ``ListSnoc.bounded, ``ListSnoc.names, ``ListSnoc.buffers,
      ``implementation, ``bounded, ``names, ``buffers, ``resources, ``reserved_room,
      ``budget, ``named, ``bufferBound, ``accepted, ``memory, ``zeroBudget, ``unitsBudget] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMHistories
