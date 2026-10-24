import Proofs.Runtime.Caliper.SchnorrROMTapeQuery
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMTapeQuery
open SchnorrROMTape

private def layout : Layouts 12 Nat where
  scalar := Layout.counter 12 4096 (by decide) (by decide)
  capacity := 6
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private theorem zeroValid : layout.scalar.valid 0 := by change 0 < 4096; decide
private def scalarRequest : Constructed layout.unit layout.counter (fun _ => 4095) :=
  Constructed.constant layout.unit layout.counter ⟨4095, by change 4095 < 4096; decide⟩ layout.wordFits
private def scalarSource : ProbComp layout.scalar.Value :=
  Fresh.naturalSource layout ⟨4095, by change 4095 < 4096; decide⟩
private def sampler : Interactive.Code 12 := .seq (.compute scalarRequest.implementation.program.code) (Fresh.naturalCode layout)
private theorem scalar_correct : Interactive.Refines (Fresh.port layout) .unit layout.unit.representation layout.scalar.representation
    (fun _ => scalarSource) sampler := by
  convert (Interactive.Refines.compute (Fresh.port layout) .unit scalarRequest.implementation.program).seq
    (Fresh.natural_refines layout) using 1 <;> rfl
private theorem scalar_time : Interactive.TimeBound (Fresh.port layout) .unit layout.unit.representation sampler 26 :=
  (Interactive.TimeBound.compute (port := Fresh.port layout) (cost := .unit) scalarRequest.implementation.program _
    scalarRequest.bounded.time_le).seq (Interactive.Refines.compute (Fresh.port layout) .unit scalarRequest.implementation.program)
      (Fresh.natural_time layout)
private theorem scalar_words : (sampler.lower (Fresh.port layout)).descriptionWords ≤ 127 := by
  have natural := Fresh.natural_words layout
  have prepared := scalarRequest.bounded.code_le
  change descriptionWords scalarRequest.implementation.program.code ≤ 40 at prepared
  simp only [sampler, Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega
private theorem scalar_names : WordIO.NamesBound (sampler.lower (Fresh.port layout)) 3 := by constructor <;> decide +kernel
private theorem scalar_fits : (sampler.lower (Fresh.port layout)).DescriptionFits :=
  .seq layout.wordFits (.compute scalarRequest.implementation.program.description_fits) (Fresh.natural_fits layout)

private def freshProgram := Fresh.code layout zeroValid sampler
private def program := Query.code layout zeroValid sampler
private theorem fresh_bounded : Interactive.TimeBound (Fresh.port layout) .unit layout.counter.representation freshProgram
    (Fresh.timeBudget layout zeroValid 26) := Fresh.time_bound layout zeroValid scalar_correct scalar_time
private theorem bounded : Interactive.TimeBound (Fresh.port layout) .unit (Read.input layout).representation program
    (Query.timeBudget layout zeroValid 26) := Query.time_bound layout zeroValid scalar_correct scalar_time
example : (program.lower (Fresh.port layout)).descriptionWords ≤ Query.codeBudget layout zeroValid 127 :=
  Query.code_bound layout zeroValid sampler scalar_words
example : (program.lower (Fresh.port layout)).memBound ≤ 7 := Query.buffers layout zeroValid sampler
example : (program.lower (Fresh.port layout)).DescriptionFits :=
  Query.descriptionFits layout zeroValid sampler scalar_fits (by change 2 < 4096; decide)

private def runFresh (tag : Fin 4096) (replies : List (Word 12)) := do
  let before := layout.counter.representation.initial ⟨tag.val, tag.isLt⟩
  let result ← WordIO.run .unit RandomTape.zero 100000 (freshProgram.lower (Fresh.port layout)) before replies
  pure ((layout.entry.representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val, result.trace, result.remaining)

private def saved : List (Schnorr.TapeCell Nat) := [(3, 0, 1), (1, 0, 0), (7, 0, 2), (1, 22, 0)]
private theorem saved_valid : (Read.saved layout).valid saved := by
  change (4 ≤ 6 ∧ ∀ cell ∈ saved, cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096) ∧ 4 < 6
  simp [saved]
private def input (tag : Fin 4096) : (Read.input layout).Value :=
  ⟨(tag.val, (0, 0, 0), saved, saved), tag.isLt,
    ⟨by change 0 < 4096; decide, by change 0 < 4096; decide, by change 0 < 4096; decide⟩,
    saved_valid, saved_valid.1⟩
private def empty : (Read.input layout).Value := ⟨(1, (0, 0, 0), [], []), by
  change 1 < 4096 ∧ (0 < 4096 ∧ 0 < 4096 ∧ 0 < 4096) ∧
    ((0 ≤ 6 ∧ ∀ cell ∈ ([] : List (Schnorr.TapeCell Nat)), layout.entry.valid cell) ∧ 0 < 6) ∧
    0 ≤ 6 ∧ ∀ cell ∈ ([] : List (Schnorr.TapeCell Nat)), layout.entry.valid cell
  simp⟩
private def run (value : (Read.input layout).Value) (replies : List (Word 12)) := do
  let initial := (Read.input layout).representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 100000 (program.lower (Fresh.port layout)) before replies
  pure (((Read.output layout).representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val,
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 10).all (fun i => result.state.caps (i + 1) == 0))

-- Uniform sampling and complete replay-cell construction share the same
-- original uniform port, including a runtime-selected maximum range.
open Lean in
run_cmd do
  for (tag, range, answer, cell) in [
      ((9 : Fin 4096), (7 : Word 12), (5 : Word 12), (9, 0, 5)),
      (2, 0, 0, (2, 0, 0)), (0, 0, 0, (0, 0, 0)),
      (4095, 4093, 4093, (4095, 0, 4093)),
      (1, 4095, 99, (1, 99, 0)), (1, 4095, 0, (1, 0, 0))] do
    unless runFresh tag [range, answer, 88] == some (some cell,
        [.output range, .invoke, .input range, .input answer], [88]) do
      throwError "fresh-cell construction forwarded the wrong range or built the wrong cell at tag {tag.val}"
  for (tag, answer, rest) in [
      ((1 : Fin 4096), (1, 0, 0), [(3, 0, 1), (7, 0, 2), (1, 22, 0)]),
      (3, (3, 0, 1), [(1, 0, 0), (7, 0, 2), (1, 22, 0)]),
      (7, (7, 0, 2), [(3, 0, 1), (1, 0, 0), (1, 22, 0)])] do
    unless run (input tag) [88] == some (some (answer, saved, rest), [], [88], #[77], 4, 91, 9, true) do
      throwError "constructed replay hit consumed randomness or changed another family"
  unless run (input 9) [7, 5, 88] ==
      some (some ((9, 0, 5), saved ++ [(9, 0, 5)], saved),
        [.output 7, .invoke, .input 7, .input 5], [88], #[77], 4, 91, 9, true) do
    throwError "constructed private replay miss did not preserve the raw query family and both tapes"
  unless run empty [4095, 0] == some (some ((1, 0, 0), [(1, 0, 0)], []),
      [.output 4095, .invoke, .input 4095, .input 0], [], #[77], 4, 91, 9, true) do
    throwError "constructed challenge replay miss lost a zero scalar"
  unless run (input 9) [] == none do throwError "a replay miss succeeded without a fresh reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``UniformQueryDraw.refines, ``UniformQueryDraw.time_bound, ``UniformQueryDraw.code_bound, ``UniformQueryDraw.resources,
      ``Constructed.subtract, ``Fresh.refines, ``Fresh.rawDraw, ``Fresh.read_rawOracle, ``Fresh.time_bound, ``Fresh.code_bound,
      ``Fresh.descriptionFits, ``Fresh.resources, ``Query.refines, ``Query.observe_rawOracle, ``Query.time_bound,
      ``Query.code_bound, ``Query.descriptionFits, ``Query.resources, ``scalar_correct, ``scalar_words, ``fresh_bounded, ``bounded] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMTapeQuery
