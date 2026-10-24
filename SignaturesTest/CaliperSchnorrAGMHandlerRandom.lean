import Proofs.Runtime.Caliper.SchnorrAGMHandlerRandomMemory
import Proofs.Runtime.Caliper.SchnorrAGMHandlerRandomSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMHandlerRandom
open CaliperBackend.SchnorrAGM.Handler.RandomComponent

private def scheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 0 0 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def layout : CaliperBackend.SchnorrAGM.Handler.Layouts 16 Nat (Word 16) (Word 16) 0 0 65535 where
  scheme := scheme
  groups := 1
  rows := 2
  coefficients := 2
  rangeFits := by decide
  counterFits := by decide
  groupCountFits := by decide
  rowCountFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide

private def fullState (malformed bad : Bool) : SchnorrAGM.Native.EncodedState (Word 16) (Word 16) Nat :=
  ([((0, 0), (0, false, 0, 0))], [(1, 0), (0, 1)], [], malformed, bad)
private theorem state_valid (malformed bad : Bool) : scheme.state.valid (fullState malformed bad) := by
  refine ⟨⟨by change 1 ≤ 1; decide, ?_⟩, ⟨by change 2 ≤ 2; decide, fun _ _ => ⟨trivial, trivial⟩⟩,
    ⟨by change 0 ≤ 0; decide, by change ∀ message ∈ ([] : List Nat), _; simp⟩, trivial, trivial⟩
  intro entry member
  change entry ∈ [((0, 0), (0, false, 0, 0))] at member
  simp only [List.mem_singleton] at member
  subst entry
  exact ⟨⟨by change 0 < 256; decide, trivial⟩, trivial, trivial, trivial, trivial⟩
private theorem valid_iff (g pk : Word 16) (n : Nat) (groups : List (Word 16)) (rows : List (List (Word 16)))
    (state : SchnorrAGM.Native.EncodedState (Word 16) (Word 16) Nat) :
    layout.randomInput.valid ((n, groups, rows), (g, pk), state) ↔
      n < 65536 ∧ groups.length ≤ 1 ∧ (rows.length ≤ 2 ∧ ∀ row ∈ rows, row.length ≤ 2) ∧ scheme.state.valid state := by
  change ((n < 65536 ∧ (groups.length ≤ 1 ∧ ∀ _ ∈ groups, True) ∧
    (rows.length ≤ 2 ∧ ∀ row ∈ rows, row.length ≤ 2 ∧ ∀ _ ∈ row, True)) ∧ (True ∧ True) ∧ scheme.state.valid state) ↔ _
  simp only [implies_true, and_true, true_and, and_assoc]
private def request (g pk : Word 16) (n : Fin 65536) (nonempty malformed bad : Bool) : layout.randomInput.Value :=
  ⟨((n.val, if nonempty then [7] else [], [[], [0, 65535]]), (g, pk), fullState malformed bad), by
    rw [valid_iff]
    refine ⟨n.isLt, ?_, by decide, state_valid malformed bad⟩
    cases nonempty <;> decide⟩

private theorem refined : Interactive.Refines layout.random.port .unit layout.randomInput.representation
    layout.randomOutput.representation (source layout) (code layout) := refines layout
private theorem timed : Interactive.TimeBound layout.random.port .unit layout.randomInput.representation
    (code layout) (timeBudget layout) := time_bound layout
private theorem stored : ((code layout).lower layout.random.port).descriptionWords ≤ codeBudget layout := code_bound layout
private theorem named : WordIO.NamesAccounted ((code layout).lower layout.random.port) 5 := names layout
private theorem boundedBuffers : ((code layout).lower layout.random.port).memBound ≤ 7 := buffers layout
private theorem fitting : ((code layout).lower layout.random.port).DescriptionFits := descriptionFits layout

private def execute (args : layout.randomInput.Value) (replies : List (Word 16)) := do
  let initial := layout.randomInput.representation.initial args
  let before := { initial with
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    regs := fun r => if r = 99 then 91 else initial.regs r
    tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 ((code layout).lower layout.random.port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200, result.state.caps 200,
    result.state.regs 99, result.state.tapePos, (List.range 10).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ timeBudget layout))

example : ¬ layout.randomInput.valid ((65536, [], []), (0, 0), fullState false false) := by
  intro invalid
  have range := invalid.1.1
  change 65536 < 65536 at range
  omega

open Lean in
run_cmd do
  for (g, pk) in ([(9, 10), (65535, 0)] : List (Word 16 × Word 16)) do
    for nonempty in [false, true] do
      for malformed in [false, true] do
        for bad in [false, true] do
          for (n, value) in ([(0, 0), (7, 3), (65535, 65535)] : List (Fin 65536 × Word 16)) do
            let expected : Array (Word 16) := #[value, 0, 0, g, pk,
              1, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 1, 0,
              if nonempty || malformed then 1 else 0, if bad then 1 else 0]
            let range : Word 16 := BitVec.ofNat 16 n.val
            let args := request g pk n nonempty malformed bad
            unless execute args [range, value, 88] ==
                some (expected, [.output range, .invoke, .input range, .input value], [88], #[77], 4, 91, 9, true, true) do
              throwError "common-store randomness lost runtime configuration, reply/state bytes, exact query trace, caller frame, scratch release or time bound"
            unless execute args [] == none && execute args [range] == none do
              throwError "common-store randomness succeeded without its complete oracle reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CaliperBackend.SchnorrAGM.Handler.Layouts.hash, ``CaliperBackend.SchnorrAGM.Handler.Layouts.signing,
      ``prepare, ``finish, ``refines, ``erase, ``reply_bound, ``time_bound, ``code_bound, ``names, ``buffers,
      ``descriptionFits, ``resources, ``source_original, ``input_valid, ``reserved_input,
      ``refined, ``timed, ``stored, ``named, ``boundedBuffers, ``fitting] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMHandlerRandom
