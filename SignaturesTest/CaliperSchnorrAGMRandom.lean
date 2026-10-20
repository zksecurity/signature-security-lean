import Signatures.Runtime.Caliper.SchnorrAGMRandomMemory
import Signatures.Runtime.Caliper.SchnorrAGMRandomSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMRandom
open CaliperBackend.SchnorrAGM.Random

private def scheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def layout : CaliperBackend.SchnorrAGM.Random.Layouts 16 Nat (Word 16) (Word 16) 1 1 65535 where
  scheme := scheme
  rangeFits := by decide
  groups := 2
  rows := 3
  coefficients := 4
  groupCountFits := by decide
  rowCountFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide

private theorem refined : Interactive.Refines layout.port .unit layout.input.representation layout.output.representation
    (source layout) (code layout) := refines layout
private theorem timed : Interactive.TimeBound layout.port .unit layout.input.representation (code layout) (timeBudget layout) := time_bound layout
private theorem stored : ((code layout).lower layout.port).descriptionWords ≤ codeBudget layout := code_bound layout
private theorem named : WordIO.NamesAccounted ((code layout).lower layout.port) 5 := names layout
private theorem boundedBuffers : ((code layout).lower layout.port).memBound ≤ 6 := buffers layout
private theorem fitting : ((code layout).lower layout.port).DescriptionFits := descriptionFits layout

private theorem valid_iff (groups : List (Word 16)) (rows : List (List (Word 16))) (n : Nat)
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    layout.input.valid (groups, rows, n, entries, basis, signed, malformed, bad) ↔
      groups.length ≤ 2 ∧ (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4) ∧ n < 65536 ∧
        (entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 3 ∧ signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256 := by
  change ((groups.length ≤ 2 ∧ ∀ group ∈ groups, True) ∧
    (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 4 ∧ ∀ coefficient ∈ row, True) ∧ n < 65536 ∧
    (entries.length ≤ 3 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 3 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ↔ _
  simp only [and_true, implies_true, and_assoc]
private def full : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)) :=
  [((3, 4), (0, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, false, 13, 14))]
private def request (n : Fin 65536) (nonempty malformed bad : Bool) : layout.input.Value :=
  ⟨(if nonempty then [4, 7] else [], [[], [65535], [5, 6, 7, 8]], n.val, full,
    [(1, 0), (0, 1), (5, 7)], [9], malformed, bad), by
    rw [valid_iff]
    refine ⟨?_, by decide, n.isLt, by decide, by decide, by decide, by decide⟩
    cases nonempty <;> decide⟩

example : ¬ layout.input.valid ([], [], 65536, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1, 2, 3], [], 0, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1], [[], [], [], []], 0, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1], [[1, 2, 3, 4, 5]], 0, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([], [], 0, [((256, 0), (0, false, 0, 0))], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1], [], 0, [], [], [256], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([], [], 0, List.replicate 4 ((0, 0), (0, false, 0, 0)), [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ([1], [], 0, [], List.replicate 4 (0, 0), [], false, false) := by rw [valid_iff]; decide

private theorem memory (tape : RandomTape 16) (args : layout.input.Value) (before : State 16)
    (holds : layout.input.representation.Holds args before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support ((code layout).execute layout.port .unit tape before)) :
    finished.time ≤ timeBudget layout ∧ ∃ answer ∈ support (source layout args),
      layout.output.representation.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape ((code layout).lower layout.port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          (((code layout).lower layout.port).staticWords registers buffers : Int) +
            between.liveMem (max buffers ((code layout).lower layout.port).memBound) ≤
              5 * codeBudget layout + 20 + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    resources layout tape args before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def execute (args : layout.input.Value) (replies : List (Word 16)) := do
  let initial := layout.input.representation.initial args
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 ((code layout).lower layout.port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
    result.state.regs 99, result.state.tapePos, (List.range 10).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ timeBudget layout))

private def zeroScheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 0 0 where
  scalar := scheme.scalar
  point := scheme.point
  message := scheme.message
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def zeroLayout : CaliperBackend.SchnorrAGM.Random.Layouts 16 Nat (Word 16) (Word 16) 0 0 0 where
  scheme := zeroScheme
  rangeFits := by decide
  groups := 1
  rows := 0
  coefficients := 0
  groupCountFits := by decide
  rowCountFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide
private def zeroRequest (nonempty : Bool) : zeroLayout.input.Value :=
  ⟨(if nonempty then [7] else [], [], 0, [((0, 0), (0, false, 0, 0))], [(1, 0), (0, 1)], [], false, true), by
    refine ⟨⟨?_, fun _ _ => trivial⟩, ⟨by change 0 ≤ 0; decide, by simp⟩, by change 0 < 1; decide,
      ⟨by change 1 ≤ 1; decide, ?_⟩, ⟨by change 2 ≤ 2; decide, fun _ _ => ⟨trivial, trivial⟩⟩,
      ⟨by change 0 ≤ 0; decide, by simp⟩, trivial, trivial⟩
    · cases nonempty <;> decide
    · intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      exact ⟨⟨by change 0 < 256; decide, trivial⟩, trivial, trivial, trivial, trivial⟩⟩
private def emptyLayout : CaliperBackend.SchnorrAGM.Random.Layouts 16 Nat (Word 16) (Word 16) 0 0 0 :=
  { zeroLayout with groups := 0, groupCountFits := by decide, storageFits := by decide }
private def emptyRequest : emptyLayout.input.Value :=
  ⟨(zeroRequest false).val, ⟨by change 0 ≤ 0; decide, fun _ _ => trivial⟩, (zeroRequest false).property.2⟩

open Lean in
run_cmd do
  for nonempty in [false, true] do
    for malformed in [false, true] do
      for bad in [false, true] do
        for (n, value) in [(0, 0), (7, 3), (65535, 65535)] do
          let expected : Array (Word 16) := #[value, 0, 0, 3, 3, 4, 0, 1, 9, 10,
            3, 4, 8, 1, 11, 12, 5, 6, 1, 0, 13, 14, 3, 1, 0, 0, 1, 5, 7, 1, 9,
            if nonempty || malformed then 1 else 0, if bad then 1 else 0]
          let range : Word 16 := BitVec.ofNat 16 n.val
          unless execute (request n nonempty malformed bad) [range, value, 88] ==
              some (expected, [.output range, .invoke, .input range, .input value], [88], #[77], 4, 91, 9, true, true) do
            throwError "random request lost its draw, runtime range, flag update, full stores, empty reply or caller frame"
          unless execute (request n nonempty malformed bad) [] == none &&
              execute (request n nonempty malformed bad) [range] == none do
            throwError "a random request succeeded without its full oracle reply, possibly skipping malformed requests"
  let small := fun program port initial replies =>
    (WordIO.run .unit RandomTape.zero 1000000 (program.lower port) initial replies).map
      (fun result => (result.state.bufs 0, result.trace, result.remaining))
  for nonempty in [false, true] do
    let expected : Array (Word 16) := #[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, if nonempty then 1 else 0, 1]
    unless small (code zeroLayout) zeroLayout.port (zeroLayout.input.representation.initial (zeroRequest nonempty)) [0, 0] ==
        some (expected, [.output 0, .invoke, .input 0, .input 0], []) do
      throwError "zero query allowances, zero range or zero row/coefficient capacities blocked randomness on full stores"
  unless small (code emptyLayout) emptyLayout.port (emptyLayout.input.representation.initial emptyRequest) [0, 0] ==
      some (#[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0, 0, 1], [.output 0, .invoke, .input 0, .input 0], []) do
    throwError "zero group capacity broke the length test or unconditional random forwarding"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CaliperBackend.SchnorrAGM.Random.test, ``mark, ``prepare, ``prepare_bounded, ``wrap,
      ``refines, ``erase, ``reply_bound, ``time_bound, ``code_bound, ``names, ``buffers, ``descriptionFits, ``resources,
      ``source_original, ``input_valid, ``reserved_input, ``refined, ``timed, ``stored, ``named, ``boundedBuffers, ``fitting, ``memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMRandom
