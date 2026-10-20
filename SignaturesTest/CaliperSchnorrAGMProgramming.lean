import Signatures.Runtime.Caliper.SchnorrAGMProgrammingBounds
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMProgramming
open CaliperBackend.SchnorrAGM.Signing.Programming

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
private def program := implementation layout
private theorem budget : program.BoundedBy (timeBudget layout) (codeBudget layout) := bounded layout
private theorem named : NamesAccounted program.program.code 5 := names layout
private theorem bufferBound : program.program.code.memBound ≤ 9 := buffers layout

private theorem valid_iff (key : Nat × Word 16) (entry : SchnorrAGM.Native.EncodedEntry (Word 16))
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16))) (reply : Word 16 × Word 16)
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    (input layout).valid ((key, entry, entries, ()), reply, basis, signed, malformed, bad) ↔
      (key.1 < 256 ∧ (entries.length ≤ 4 ∧ ∀ stored ∈ entries, stored.1.1 < 256) ∧
        basis.length ≤ 4 ∧ signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧
        ((lookupValue key entry entries).1 = false → entries.length ≤ 3) := by
  change (((key.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True) ∧
    (entries.length ≤ 4 ∧ ∀ stored ∈ entries, (stored.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧ True) ∧
    (True ∧ True) ∧ (basis.length ≤ 4 ∧ ∀ pair ∈ basis, True ∧ True) ∧
    (signed.length ≤ 2 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _ ↔ _
  simp only [and_true, true_and, implies_true, and_assoc]
  rfl

private def miss : (input layout).Value :=
  ⟨(((7, 23), (2, false, 0, 0), [((5, 6), (1, true, 13, 14))], ()),
    (23, 11), [(1, 0), (0, 1), (11, 65534)], [3, 7], false, false), by rw [valid_iff]; decide⟩
private def fullHit : (input layout).Value :=
  ⟨(((3, 4), (3, false, 0, 0),
    [((3, 4), (0, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14)), ((8, 9), (3, true, 15, 16))], ()),
    (31, 8), [(1, 0), (0, 1), (5, 7), (8, 9)], [7, 7], true, true), by rw [valid_iff]; decide⟩
private def lastSlot : (input layout).Value :=
  ⟨(((3, 5), (5, true, 11, 12),
    [((3, 4), (0, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14))], ()),
    (42, 99), [(5, 7), (1, 0), (0, 1)], [255, 9], false, true), by rw [valid_iff]; decide⟩
private def empty : (input layout).Value :=
  ⟨(((0, 0), (0, false, 0, 0), [], ()), (0, 0), [], [], true, false), by rw [valid_iff]; decide⟩

example : ¬ (input layout).valid (((9, 9), (0, false, 0, 0), fullHit.val.1.2.2.1, ()), fullHit.val.2) := by
  rw [valid_iff]; decide
example : ¬ (input layout).valid (((256, 0), (0, false, 0, 0), [], ()), (0, 0), [], [], false, false) := by
  rw [valid_iff]; decide
example : ¬ (input layout).valid (((0, 0), (0, false, 0, 0), [((256, 0), (0, false, 0, 0))], ()),
    (0, 0), [], [], false, false) := by rw [valid_iff]; decide
example : ¬ (input layout).valid (((0, 0), (0, false, 0, 0), [], ()), (0, 0), [], [256], false, false) := by
  rw [valid_iff]; decide
example : ¬ (input layout).valid (((0, 0), (0, false, 0, 0), [], ()), (0, 0), List.replicate 5 (0, 0), [], false, false) := by
  rw [valid_iff]; decide
example : ¬ (input layout).valid (((0, 0), (0, false, 0, 0), [], ()), (0, 0), [], [1, 2, 3], false, false) := by
  rw [valid_iff]; decide
example : ¬ (input layout).valid (((0, 0), (0, false, 0, 0), List.replicate 5 ((0, 0), (0, false, 0, 0)), ()),
    (0, 0), [], [], false, false) := by rw [valid_iff]; decide

private theorem memory (tape : RandomTape 16) (args : (input layout).Value) (before : State 16)
    (holds : (input layout).representation.Holds args before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape program.program.code before after (program.program.time args) net peak ∧
      (output layout).representation.Holds ⟨value args.val, program.preserves args.val args.property⟩ after ∧
      program.program.time args ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape program.program.code before between ∨ between = after) →
        (staticWords program.program.code registers buffers : Int) + between.liveMem (max buffers program.program.code.memBound) ≤
          5 * codeBudget layout + 20 + registers + 3 * buffers + before.liveMem buffers + timeBudget layout :=
  resources layout tape args before holds registers buffers initialRegisters initialBuffers

private def execute (args : (input layout).Value) :=
  let initial := (input layout).representation.initial args
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
  unless execute miss == some
      (#[23, 11, 2, 7, 23, 2, 0, 0, 0, 5, 6, 1, 1, 13, 14] ++ Array.replicate 12 0 ++
        #[3, 1, 0, 0, 1, 11, 65534, 0, 0, 2, 3, 7, 0, 0], #[77], 4, 91, 9, true, true) do
    throwError "signing programming lost a fresh challenge, existing entry, history, signature, framing, scratch cleanup or time bound"
  unless execute fullHit == some
      (#[31, 8, 4, 3, 4, 0, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 0, 13, 14, 8, 9, 3, 1, 15, 16,
        4, 1, 0, 0, 1, 5, 7, 8, 9, 2, 7, 7, 1, 1], #[77], 4, 91, 9, true, true) do
    throwError "full-table hit changed cached zero, affine explanations, shadowed duplicate, full histories or flags"
  unless execute lastSlot == some
      (#[42, 99, 4, 3, 5, 5, 1, 11, 12, 3, 4, 0, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 0, 13, 14,
        3, 5, 7, 1, 0, 0, 1, 0, 0, 2, 255, 9, 0, 1], #[77], 4, 91, 9, true, true) do
    throwError "final-slot miss conflated different point keys or changed reordered histories or supplied affine entry"
  unless execute empty == some
      (#[0, 0, 1] ++ Array.replicate 36 0 ++ #[1, 0], #[77], 4, 91, 9, true, true) do
    throwError "empty-table zero insertion changed signature or empty histories"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``implementation, ``bounded, ``names, ``buffers, ``resources, ``source, ``reserved_admissible,
      ``budget, ``named, ``bufferBound, ``memory, ``cache_source] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMProgramming
