import Proofs.Runtime.Caliper.SchnorrROMTapeReadMemory
import Proofs.Runtime.Caliper.SchnorrROMTapeReadSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMTapeRead
open SchnorrROMTape

private def layout : Layouts 12 Nat where
  scalar := Layout.counter 12 4096 (by decide) (by decide)
  capacity := 6
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def sampleSpec : OracleSpec Nat := fun _ => layout.entry.Value
private def packet := layout.counter.prod layout.entry (by decide)
private def packetView : (Σ _ : layout.counter.Value, layout.entry.Value) ≃ packet.Value where
  toFun value := ⟨(value.1.val, value.2.val), value.1.property, value.2.property⟩
  invFun value := ⟨⟨value.val.1, value.property.1⟩, ⟨value.val.2, value.property.2⟩⟩
  left_inv value := by rcases value with ⟨⟨tag, tagValid⟩, ⟨cell, cellValid⟩⟩; rfl
  right_inv _ := rfl
private def port : Interactive.Port 12 sampleSpec where
  Request := layout.counter.Value
  source := Subtype.val
  request := layout.counter.representation
  reply := packet.representation.transport packetView
private def drawSource (tag : layout.counter.Value) : OracleComp sampleSpec layout.entry.Value :=
  sampleSpec.query tag.val
-- The oracle reply contains its request tag. Removing it is an actual copy.
private def project : Constructed packet layout.entry Prod.snd :=
  Constructed.second layout.counter layout.entry layout.wordFits packet.representation.fits
private def draw : Interactive.Code 12 := .seq .query (.compute project.implementation.program.code)
private theorem draw_correct : Interactive.Refines port .unit layout.counter.representation layout.entry.representation drawSource draw := by
  have queried := (Interactive.Refines.query port .unit).viewOutput packet.representation packetView (fun _ => rfl)
  convert queried.seq (Interactive.Refines.compute port .unit project.implementation.program) using 1 <;> rfl
private theorem draw_time : Interactive.TimeBound port .unit layout.counter.representation draw
    (WordIO.exchangeTime .unit 1 4 + project.budget.time) :=
  Interactive.TimeBound.query.seq (Interactive.Refines.query port .unit)
    ((Interactive.TimeBound.compute (port := port) (cost := .unit) project.implementation.program _ project.bounded.time_le).viewInput
      port.reply packetView (fun _ => rfl))
private theorem draw_names : WordIO.NamesBound (draw.lower port) 3 := by constructor <;> decide +kernel
private theorem draw_fits : (draw.lower port).DescriptionFits :=
  .seq layout.wordFits (WordIO.exchange_descriptionFits 1 4 (by decide) (by decide))
    (.compute project.implementation.program.description_fits)
private def program := Read.code layout port draw
private def totalTime := Read.timeBudget layout (WordIO.exchangeTime .unit 1 4 + project.budget.time)
private def totalWords := Read.codeBudget layout (draw.lower port).descriptionWords
private theorem bounded : Interactive.TimeBound port .unit (Read.input layout).representation program totalTime :=
  Read.time_bound layout port draw_correct draw_time
example : (program.lower port).descriptionWords ≤ totalWords := Read.code_bound layout port draw (Nat.le_refl _)
example : (program.lower port).memBound ≤ 7 := Read.buffers layout port draw
example : (program.lower port).DescriptionFits := Read.descriptionFits layout port draw draw_fits draw_names (by decide)

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
example : ¬(Read.input layout).valid (1, (0, 0, 0), saved ++ [(3, 0, 0), (1, 33, 0)], []) := by
  intro valid
  have impossible : 6 < 6 := valid.2.2.1.2
  omega

private def run (value : (Read.input layout).Value) (replies : List (Word 12)) := do
  let initial := (Read.input layout).representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 100000 (program.lower port) before replies
  pure (((Read.output layout).representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val,
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 10).all (fun i => result.state.caps (i + 1) == 0))

open Lean in
run_cmd do
  for (tag, answer, rest) in [
      ((1 : Fin 4096), (1, 0, 0), [(3, 0, 1), (7, 0, 2), (1, 22, 0)]),
      (3, (3, 0, 1), [(1, 0, 0), (7, 0, 2), (1, 22, 0)]),
      (7, (7, 0, 2), [(3, 0, 1), (1, 0, 0), (1, 22, 0)])] do
    unless run (input tag) [88] == some (some (answer, saved, rest), [], [88], #[77], 4, 91, 9, true) do
      throwError "hit drew randomness or changed replay order for family {tag.val}"
  unless run (input 9) [9, 9, 0, 5, 88] ==
      some (some ((9, 0, 5), saved ++ [(9, 0, 5)], saved),
        [.output 9, .invoke, .input 9, .input 9, .input 0, .input 5], [88], #[77], 4, 91, 9, true) do
    throwError "miss did not draw once, append chronologically and preserve the remaining tape"
  unless run empty [1, 1, 0, 0] == some (some ((1, 0, 0), [(1, 0, 0)], []),
      [.output 1, .invoke, .input 1, .input 1, .input 0, .input 0], [], #[77], 4, 91, 9, true) do
    throwError "a fresh zero challenge was not stored"
  unless run (input 9) [] == none do throwError "a miss succeeded without its fresh reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Constructed.viewOutput, ``Read.refines, ``Read.denote_value, ``Read.rawOracle,
      ``Read.observe_rawOracle, ``Read.time_bound, ``Read.code_bound,
      ``Read.names, ``Read.descriptionFits, ``Read.buffers, ``Read.resources, ``draw_correct, ``bounded] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMTapeRead
