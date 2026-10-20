import Signatures.Runtime.Caliper.WeightedRecord
import Lean

/-! Different hash/sign request widths and capacities, with no finite-domain
assumption on either request type. Run both log orders and account for all
stored code, caller state and intermediate copying. -/
namespace SignaturesTest.CaliperWeightedRecord
open Caliper Signatures.Runtime.CaliperBackend BoundedSource

private def number : Layout 16 Nat := Layout.counter 16 256 (by decide) (by decide)
private def point : Layout 16 (Word 16) := Layout.all (wordRepresentation 16 (by decide))
private def index := number.prod number (by decide)
private def hashEntry := index.prod point (by decide)
private def signEntry := number.prod point (by decide)
private def hashes := hashEntry.boundedList 2 (by decide) (by decide)
private def signatures := signEntry.boundedList 3 (by decide) (by decide)
private def hashLayout : WeightedRecord.Layouts 16 ((Nat × Nat) × Word 16) (List (Nat × Word 16)) :=
  ⟨hashEntry, signatures, 1, by decide, by decide, by decide⟩
private def signLayout : WeightedRecord.Layouts 16 (Nat × Word 16) (List ((Nat × Nat) × Word 16)) :=
  ⟨signEntry, hashes, 2, by decide, by decide, by decide⟩

private instance : DecidablePred hashLayout.leftInput.valid := by
  intro value
  change Decidable (((((value.1.1.1 < 256 ∧ value.1.1.2 < 256) ∧ True) ∧
    (value.2.1.length ≤ 2 ∧ ∀ entry ∈ value.2.1, (entry.1.1 < 256 ∧ entry.1.2 < 256) ∧ True) ∧
    (value.2.2.length ≤ 3 ∧ ∀ entry ∈ value.2.2, entry.1 < 256 ∧ True))) ∧ value.2.1.length ≤ 1)
  infer_instance
private instance : DecidablePred signLayout.rightInput.valid := by
  intro value
  change Decidable ((((value.1.1 < 256 ∧ True) ∧
    (value.2.1.length ≤ 2 ∧ ∀ entry ∈ value.2.1, (entry.1.1 < 256 ∧ entry.1.2 < 256) ∧ True) ∧
    (value.2.2.length ≤ 3 ∧ ∀ entry ∈ value.2.2, entry.1 < 256 ∧ True))) ∧ value.2.2.length ≤ 2)
  infer_instance

private def hashInput : hashLayout.leftInput.Value :=
  ⟨(((7, 8), 11), [((2, 3), 5)], [(4, 5), (6, 7), (8, 9)]), by decide⟩
private def signInput : signLayout.rightInput.Value :=
  ⟨((7, 11), [((1, 2), 3), ((4, 5), 6)], [(8, 9), (10, 12)]), by decide⟩
private def repeated : hashLayout.leftInput.Value :=
  ⟨(((7, 8), 11), [((7, 8), 11)], []), by decide⟩

private def run {A B : Type} {input : Layout 16 A} {output : Layout 16 B} {f : A → B}
    (implementation : Implementation .unit input output f) (value : input.Value) := do
  let initial := input.representation.initial value
  let before := { initial with
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 4 else initial.caps buffer
    regs := fun register => if register = 99 then 91 else initial.regs register
    tapePos := 9 }
  let (after, elapsed, _, _) ← Caliper.run .unit RandomTape.zero 10000 implementation.program.code before
  let result ← output.representation.encoding.decode (after.bufs 0).toList
  pure (result.val, after.bufs 200, after.caps 200, after.regs 99, after.tapePos,
    (List.range 10).all (fun buffer => after.caps (buffer + 1) == 0), elapsed)

-- The selected full log is rejected; a full other log is allowed and preserved.
example : ¬ hashLayout.leftInput.valid
    (((7, 8), 11), [((1, 2), 3), ((4, 5), 6)], []) := by decide
example : ¬ signLayout.rightInput.valid
    ((7, 11), [], [(1, 2), (3, 4), (5, 6)]) := by decide
example : ¬ hashLayout.leftInput.valid (((256, 8), 11), [], []) := by decide
example : ¬ signLayout.rightInput.valid ((7, 11), [((256, 2), 3)], []) := by decide

private theorem hashBound :
    (WeightedRecord.left hashLayout).BoundedBy 337 1171 :=
  WeightedRecord.left_bounded hashLayout
private theorem signBound :
    (WeightedRecord.right signLayout).BoundedBy 585 2007 :=
  WeightedRecord.right_bounded signLayout

-- This is a bound on every intermediate state of the same execution that
-- returns the specified logs, including arbitrary caller-owned initial state.
private theorem hashMemory (tape : RandomTape 16) (value : hashLayout.leftInput.Value)
    (before : State 16) (holds : hashLayout.leftInput.representation.Holds value before)
    (registers buffers : Nat) (regBound : RegisterBound before registers)
    (bufBound : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (WeightedRecord.left hashLayout).program.code
        before after ((WeightedRecord.left hashLayout).program.time value) net peak ∧
      hashLayout.leftOutput.representation.Holds
        ⟨WeightedRecord.leftValue value.val, WeightedRecord.preserves hashLayout value.val value.property⟩ after ∧
      (WeightedRecord.left hashLayout).program.time value ≤ 337 ∧
      ∀ between, (Caliper.Reaches .unit tape (WeightedRecord.left hashLayout).program.code before between ∨ between = after) →
        (staticWords (WeightedRecord.left hashLayout).program.code registers buffers : Int) +
          between.liveMem (max buffers (WeightedRecord.left hashLayout).program.code.memBound) ≤
            5 * 1171 + registers + 3 * buffers + before.liveMem buffers + 337 := by
  obtain ⟨after, net, peak, execution, output, elapsed, memory⟩ :=
    hashBound.memoryBound (WeightedRecord.left_names hashLayout 0)
      tape value before holds registers buffers regBound bufBound
  exact ⟨after, net, peak, execution, output, elapsed, fun between reached => (memory between reached).2.2.2⟩

open Lean in
run_cmd do
  for (value, expected) in [
      (hashInput, ([((7, 8), (11 : Word 16)), ((2, 3), 5)], [(4, 5), (6, 7), (8, 9)])),
      (repeated, ([((7, 8), (11 : Word 16)), ((7, 8), 11)], []))] do
    match run (WeightedRecord.left hashLayout) value with
    | none => throwError "hash log update failed"
    | some (answer, framed, capacity, register, tape, scratch, elapsed) =>
      unless answer == expected && framed == #[77] && capacity == 4 && register == 91 &&
          tape == 9 && scratch && elapsed ≤ 337 do
        throwError "hash log update lost entries, independent signing log, framing, or time bound"
  match run (WeightedRecord.right signLayout) signInput with
  | none => throwError "signing log update failed"
  | some (answer, framed, capacity, register, tape, scratch, elapsed) =>
    unless answer == ([((1, 2), 3), ((4, 5), 6)], [(7, 11), (8, 9), (10, 12)]) &&
        framed == #[77] && capacity == 4 && register == 91 && tape == 9 && scratch && elapsed ≤ 585 do
      throwError "signing log update lost entries, independent hash log, framing, or time bound"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``WeightedRecord.left_bounded, ``WeightedRecord.right_bounded,
      ``WeightedRecord.left_names, ``WeightedRecord.right_names,
      ``WeightedRecord.hash_source, ``WeightedRecord.sign_source, ``hashMemory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperWeightedRecord
