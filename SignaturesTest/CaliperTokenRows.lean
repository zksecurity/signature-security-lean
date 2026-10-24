import Proofs.Runtime.Caliper.TokenRowsSource
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource

namespace SignaturesTest.CaliperTokenRows

private def numbers : AttachRows.Layouts 10 Nat Nat where
  key := Layout.counter 10 1024 (by decide) (by decide)
  value := Layout.counter 10 1024 (by decide) (by decide)
  capacity := 3
  coefficients := 4
  wordFits := by decide
  counterFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide
private def noKeys : AttachRows.Layouts 10 Nat Nat :=
  { numbers with capacity := 0, counterFits := by decide, storageFits := by decide }
private def noCoefficients : AttachRows.Layouts 10 Nat Nat :=
  { numbers with coefficients := 0, coefficientCountFits := by decide, storageFits := by decide }
private def units : AttachRows.Layouts 8 Unit Unit where
  key := DataImplementation.unitLayout 8
  value := DataImplementation.unitLayout 8
  capacity := 3
  coefficients := 4
  wordFits := by decide
  counterFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide

private def exactValues : numbers.input.Value := ⟨([5, 6, 5], 99, [11, 22, 33]), by
  change (3 ≤ 3 ∧ ∀ k ∈ [5, 6, 5], k < 1024) ∧ 99 < 1024 ∧ 3 ≤ 4 ∧ ∀ v ∈ [11, 22, 33], v < 1024
  simp⟩
private def surplus : numbers.input.Value := ⟨([5, 6, 5], 99, [11, 22, 33, 44]), by
  change (3 ≤ 3 ∧ ∀ k ∈ [5, 6, 5], k < 1024) ∧ 99 < 1024 ∧ 4 ≤ 4 ∧ ∀ v ∈ [11, 22, 33, 44], v < 1024
  simp⟩
private def missing : numbers.input.Value := ⟨([5, 6], 99, [11]), by
  change (2 ≤ 3 ∧ ∀ k ∈ [5, 6], k < 1024) ∧ 99 < 1024 ∧ 1 ≤ 4 ∧ ∀ v ∈ [11], v < 1024
  simp⟩
private def emptyKeys : numbers.input.Value := ⟨([], 99, [11, 22, 33, 44]), by
  change (0 ≤ 3 ∧ ∀ k ∈ ([] : List Nat), k < 1024) ∧ 99 < 1024 ∧ 4 ≤ 4 ∧ ∀ v ∈ [11, 22, 33, 44], v < 1024
  simp⟩
private def emptyCoefficients : numbers.input.Value := ⟨([5, 6, 5], 99, []), by
  change (3 ≤ 3 ∧ ∀ k ∈ [5, 6, 5], k < 1024) ∧ 99 < 1024 ∧ 0 ≤ 4 ∧ ∀ v ∈ ([] : List Nat), v < 1024
  simp⟩
private def zeroKeys : noKeys.input.Value := ⟨([], 99, [11, 22]), by
  change (0 ≤ 0 ∧ ∀ k ∈ ([] : List Nat), k < 1024) ∧ 99 < 1024 ∧ 2 ≤ 4 ∧ ∀ v ∈ [11, 22], v < 1024
  simp⟩
private def zeroCoefficients : noCoefficients.input.Value := ⟨([5, 6, 5], 99, []), by
  change (3 ≤ 3 ∧ ∀ k ∈ [5, 6, 5], k < 1024) ∧ 99 < 1024 ∧ 0 ≤ 0 ∧ ∀ v ∈ ([] : List Nat), v < 1024
  simp⟩
private def zeroWords : units.input.Value := ⟨([(), (), ()], (), [(), ()]), by
  change (3 ≤ 3 ∧ ∀ k ∈ [(), (), ()], True) ∧ True ∧ 2 ≤ 4 ∧ ∀ v ∈ [(), ()], True
  simp⟩
private def lastStage : Fin numbers.capacity := ⟨2, by change 2 < 3; decide⟩
private def lastInput : (numbers.body lastStage).Value := ⟨(5, (2, [(6, 22), (5, 11)]), (99, [11, 22, 33, 44])), by
  change 5 < 1024 ∧ (2 < 3 ∧ 2 ≤ 2 ∧ ∀ row ∈ [(6, 22), (5, 11)], row.1 < 1024 ∧ row.2 < 1024) ∧
    99 < 1024 ∧ 4 ≤ 4 ∧ ∀ v ∈ [11, 22, 33, 44], v < 1024
  simp⟩

-- A token stores both message and the actual returned point. Equal messages
-- with different points are distinct chronological occurrences.
private def tokens : AttachRows.Layouts 10 (Nat × Nat) Nat :=
  { numbers with key := numbers.key.prod numbers.key (by change 1 + 1 < 1024; decide), storageFits := by decide }
private def zero : tokens.value.Value := ⟨0, by change 0 < 1024; decide⟩
private def transcript : (TokenRows.input tokens).Value := ⟨([(5, 11), (6, 22), (5, 33)], [9, 8]), by
  change (3 ≤ 3 ∧ ∀ k ∈ [(5, 11), (6, 22), (5, 33)], k.1 < 1024 ∧ k.2 < 1024) ∧
    2 ≤ 4 ∧ ∀ v ∈ [9, 8], v < 1024
  simp⟩
private def extraCoefficients : (TokenRows.input tokens).Value := ⟨([(5, 11), (6, 22)], [9, 8, 7, 6]), by
  change (2 ≤ 3 ∧ ∀ k ∈ [(5, 11), (6, 22)], k.1 < 1024 ∧ k.2 < 1024) ∧
    4 ≤ 4 ∧ ∀ v ∈ [9, 8, 7, 6], v < 1024
  simp⟩
private def emptyTranscript : (TokenRows.input tokens).Value := ⟨([], [9, 8, 7, 6]), by
  change (0 ≤ 3 ∧ ∀ k ∈ ([] : List (Nat × Nat)), k.1 < 1024 ∧ k.2 < 1024) ∧
    4 ≤ 4 ∧ ∀ v ∈ [9, 8, 7, 6], v < 1024
  simp⟩

example : ¬ numbers.input.valid ([1, 2, 3, 4], 0, []) := by
  intro valid
  have impossible : 4 ≤ 3 := valid.1.1
  omega
example : ¬ numbers.input.valid ([], 0, [1, 2, 3, 4, 5]) := by
  intro valid
  have impossible : 5 ≤ 4 := valid.2.2.1
  omega
example : ¬ numbers.input.valid ([1024], 0, []) := by
  intro valid
  have impossible : 1024 < 1024 := valid.1.2 1024 (by simp)
  omega
example : ¬ numbers.input.valid ([], 1024, []) := by
  intro valid
  have impossible : 1024 < 1024 := valid.2.1
  omega
example : ¬ (numbers.body lastStage).valid (5, (3, []), (99, [])) := by
  intro valid
  have impossible : 3 < 3 := valid.2.1.1
  omega
example : (AttachRows.implementation numbers).program.code.memBound ≤ 10 := AttachRows.buffers numbers
example : (TokenRows.implementation tokens zero).program.code.memBound ≤ 10 := TokenRows.buffers tokens zero
example : NamesAccounted (TokenRows.implementation tokens zero).program.code 0 := TokenRows.names tokens zero 0
example : DescriptionFits (TokenRows.implementation tokens zero).program.code := (TokenRows.implementation tokens zero).program.description_fits
private theorem bound : (TokenRows.implementation tokens zero).BoundedBy
    (TokenRows.timeBudget tokens) (TokenRows.codeBudget tokens) := TokenRows.bounded tokens zero

private def run {w : Nat} {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (implementation : Implementation .unit input output f) (value : input.Value) :=
  let initial := input.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  (Caliper.run .unit RandomTape.zero 10000 implementation.program.code before).map fun result =>
    (result.1.bufs 0, result.1.bufs 200, result.1.caps 200, result.1.regs 99, result.1.tapePos,
      (List.range 16).all (fun i => result.1.caps (i + 1) == 0))

open Lean in
run_cmd do
  for (value, expected) in [(exactValues, #[3, 5, 11, 6, 22, 5, 33]), (surplus, #[3, 5, 11, 6, 22, 5, 33]),
      (missing, #[2, 5, 11, 6, 99, 0, 0]), (emptyKeys, #[0, 0, 0, 0, 0, 0, 0]),
      (emptyCoefficients, #[3, 5, 99, 6, 99, 5, 99])] do
    unless run (AttachRows.implementation numbers) value == some (expected, #[77], 4, 91, 9, true) do
      throwError "row attachment failed for {value.val}"
  unless run (AttachRows.implementation noKeys) zeroKeys == some (#[0], #[77], 4, 91, 9, true) do
    throwError "zero-capacity key list failed"
  unless run (AttachRows.implementation noCoefficients) zeroCoefficients == some (#[3, 5, 99, 6, 99, 5, 99], #[77], 4, 91, 9, true) do
    throwError "zero-capacity coefficient list lost the runtime default"
  unless run (AttachRows.implementation units) zeroWords == some (#[3], #[77], 4, 91, 9, true) do
    throwError "zero-word keys and coefficients lost their row count"
  unless run (AttachRows.body numbers lastStage) lastInput == some (#[3, 3, 5, 33, 6, 22, 5, 11], #[77], 4, 91, 9, true) do
    throwError "last attachment step failed to increment or prepend"
  unless run (TokenRows.implementation tokens zero) transcript == some (#[3, 5, 33, 9, 6, 22, 8, 5, 11, 0], #[77], 4, 91, 9, true) do
    throwError "chronological coefficient rows lost duplicate-message occurrences or missing zero defaults"
  unless run (TokenRows.implementation tokens zero) extraCoefficients == some (#[2, 6, 22, 9, 5, 11, 8, 0, 0, 0], #[77], 4, 91, 9, true) do
    throwError "surplus coefficients created rows or changed chronology"
  unless run (TokenRows.implementation tokens zero) emptyTranscript == some (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[77], 4, 91, 9, true) do
    throwError "empty chronological transcript was not padded"
  unless (AttachRows.implementation numbers).program.time exactValues < (AttachRows.implementation numbers).program.time surplus do
    throwError "surplus coefficient storage must remain traversed and charged"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``AttachRows.advance, ``AttachRows.body, ``AttachRows.body_bounded, ``AttachRows.body_names,
      ``AttachRows.accepted, ``AttachRows.loop_buffers, ``AttachRows.source_result, ``AttachRows.implementation,
      ``AttachRows.bounded, ``AttachRows.buffers, ``AttachRows.names, ``AttachRows.static_bound, ``AttachRows.resources,
      ``TokenRows.implementation, ``TokenRows.bounded, ``TokenRows.buffers, ``TokenRows.names,
      ``TokenRows.static_bound, ``TokenRows.resources, ``TokenRows.source, ``TokenRows.source_bounded,
      ``TokenRows.source_buffers, ``TokenRows.source_names, ``bound] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperTokenRows
