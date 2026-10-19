import Signatures.Runtime.Caliper.BLSChronological
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperBLSChronological

-- Infinite source naturals are admitted only when their stored word fits.
private def numbers : ListReverse.Layouts 8 Nat where
  entry := Layout.counter 8 256 (by decide) (by decide)
  capacity := 3
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def zeroCapacity : ListReverse.Layouts 8 Nat :=
  { numbers with capacity := 0, countFits := by decide, storageFits := by decide }
private def tokens : ListReverse.Layouts 8 Unit where
  entry := DataImplementation.unitLayout 8
  capacity := 3
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def nilValue : numbers.list.Value := ⟨[], by exact ⟨by decide, by simp⟩⟩
private def shortValue : numbers.list.Value := ⟨[2, 5], by
  change 2 ≤ 3 ∧ ∀ value ∈ [2, 5], value < 256
  simp⟩
private def fullValue : numbers.list.Value := ⟨[2, 5, 7], by
  change 3 ≤ 3 ∧ ∀ value ∈ [2, 5, 7], value < 256
  simp⟩
private def noSlots : zeroCapacity.list.Value := ⟨[], by exact ⟨by decide, by simp⟩⟩
private def zeroWidth : tokens.list.Value := ⟨[(), (), ()], by
  exact ⟨by decide, fun _ _ => trivial⟩⟩

example : ¬ numbers.list.valid [1, 2, 3, 4] := by
  intro valid
  have impossible : 4 ≤ 3 := valid.1
  omega
example : ¬ numbers.list.valid [256] := by
  intro valid
  have impossible : 256 < 256 := valid.2 256 (by simp)
  omega
example : ¬ zeroCapacity.list.valid [1] := by
  intro valid
  have impossible : 1 ≤ 0 := valid.1
  omega

private def records : BLSRecord.Layouts 10 Nat (Word 10) where
  message := Layout.counter 10 1024 (by decide) (by decide)
  point := Layout.all (wordRepresentation 10 (by decide))
  capacityPred := 2
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def transcript : records.transcript.Value :=
  ⟨([(5, 123), (6, 456), (5, 789)], [(8, 91), (9, 92)]), by
    change (3 ≤ 3 ∧ ∀ entry ∈ [(5, 123), (6, 456), (5, 789)], entry.1 < 1024 ∧ True) ∧
      (2 ≤ 3 ∧ ∀ entry ∈ [(8, 91), (9, 92)], entry.1 < 1024 ∧ True)
    simp⟩
private def emptyTranscript : records.transcript.Value := ⟨([], []), by
  constructor <;> exact ⟨by decide, by simp⟩⟩

private theorem reversed_bound : (ListReverse.implementation numbers).BoundedBy
    (ListReverse.timeBudget numbers) (ListReverse.codeBudget numbers) := ListReverse.bounded numbers
private theorem chronological_bound : (BLSChronological.implementation records).BoundedBy
    (BLSChronological.timeBudget records) (BLSChronological.codeBudget records) := BLSChronological.bounded records
example : (ListReverse.implementation numbers).program.code.memBound ≤ 3 := ListReverse.buffers numbers
example : (BLSChronological.implementation records).program.code.memBound ≤ 4 := BLSChronological.buffers records
example : NamesAccounted (BLSChronological.implementation records).program.code 0 := BLSChronological.names records 0
example : DescriptionFits (BLSChronological.implementation records).program.code :=
  (BLSChronological.implementation records).program.description_fits

private theorem chronological_memory (tape : RandomTape 10) (value : records.transcript.Value) (before : State 10)
    (holds : records.transcript.representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (BLSChronological.implementation records).program.code before after
      ((BLSChronological.implementation records).program.time value) net peak ∧
      records.transcript.representation.Holds
        ⟨LazyAGM.chronological value.val, (BLSChronological.implementation records).preserves value.val value.property⟩ after ∧
      (BLSChronological.implementation records).program.time value ≤ BLSChronological.timeBudget records ∧
      ∀ between, (Caliper.Reaches .unit tape (BLSChronological.implementation records).program.code before between ∨ between = after) →
        (staticWords (BLSChronological.implementation records).program.code registers buffers : Int) +
          between.liveMem (max buffers (BLSChronological.implementation records).program.code.memBound) ≤
          5 * BLSChronological.codeBudget records + registers + 3 * buffers + before.liveMem buffers + BLSChronological.timeBudget records :=
  BLSChronological.resources records tape value before holds registers buffers initialRegisters initialBuffers

private def run {w : Nat} {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (implementation : Implementation .unit input output f) (value : input.Value) :=
  let initial := input.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 10000 implementation.program.code before).map fun result =>
    (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 10).all (fun i => result.1.caps (i + 1) == 0))

open Lean in
run_cmd do
  unless run (ListReverse.implementation numbers) nilValue == some (#[0, 0, 0, 0], #[77], 4, 91, 9, true) do
    throwError "empty reversal failed its final padding conversion"
  unless run (ListReverse.implementation numbers) shortValue == some (#[2, 5, 2, 0], #[77], 4, 91, 9, true) do
    throwError "partial reversal failed to reverse entries and pad unused capacity"
  unless run (ListReverse.implementation numbers) fullValue == some (#[3, 7, 5, 2], #[77], 4, 91, 9, true) do
    throwError "full reversal lost entries or retained scratch capacity"
  unless run (ListReverse.implementation zeroCapacity) noSlots == some (#[0], #[77], 4, 91, 9, true) do
    throwError "zero-capacity reversal failed"
  unless run (ListReverse.implementation tokens) zeroWidth == some (#[3], #[77], 4, 91, 9, true) do
    throwError "zero-word entries lost their list count"
  unless run (BLSChronological.implementation records) transcript ==
      some (#[3, 5, 789, 6, 456, 5, 123, 2, 9, 92, 8, 91, 0, 0], #[77], 4, 91, 9, true) do
    throwError "BLS chronological preparation lost duplicate-message occurrences or crossed log boundaries"
  unless run (BLSChronological.implementation records) emptyTranscript ==
      some (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[77], 4, 91, 9, true) do
    throwError "empty BLS transcript lost its independent log capacities"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``FoldStep.buffers, ``StagedFold.accept, ``ListReverse.accepted, ``ListReverse.loop_buffers,
      ``ListReverse.implementation, ``ListReverse.reverse_fold, ``ListReverse.bounded, ``ListReverse.buffers,
      ``ListReverse.names, ``ListReverse.static_bound, ``ListReverse.resources,
      ``BLSChronological.implementation, ``BLSChronological.bounded, ``BLSChronological.buffers,
      ``BLSChronological.names, ``BLSChronological.resources, ``reversed_bound, ``chronological_bound, ``chronological_memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperBLSChronological
