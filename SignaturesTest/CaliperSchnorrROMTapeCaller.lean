import Proofs.Runtime.Caliper.SchnorrROMTapeCallerMemory
import Proofs.Runtime.Caliper.SchnorrROMTapeCallerSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrROMTapeCaller
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

private def privateProgram := Caller.privateCode layout zeroValid sampler
private def scalarProgram := Caller.scalarCode layout zeroValid sampler
private theorem private_bounded : Interactive.TimeBound (Fresh.port layout) .unit (Caller.privateInput layout).representation
    privateProgram (Caller.privateTime layout zeroValid 26) := Caller.private_time layout zeroValid scalar_correct scalar_time
private theorem scalar_bounded : Interactive.TimeBound (Fresh.port layout) .unit (Read.store layout).representation
    scalarProgram (Caller.scalarTime layout zeroValid 26) := Caller.scalar_time layout zeroValid scalar_correct scalar_time
example : (privateProgram.lower (Fresh.port layout)).descriptionWords ≤ Caller.privateWords layout zeroValid 127 :=
  Caller.private_words layout zeroValid sampler scalar_words
example : (scalarProgram.lower (Fresh.port layout)).descriptionWords ≤ Caller.scalarWords layout zeroValid 127 :=
  Caller.scalar_words layout zeroValid sampler scalar_words
example : (privateProgram.lower (Fresh.port layout)).memBound ≤ 8 := Caller.private_buffers layout zeroValid sampler
example : (scalarProgram.lower (Fresh.port layout)).memBound ≤ 7 := Caller.scalar_buffers layout zeroValid sampler
example : (privateProgram.lower (Fresh.port layout)).DescriptionFits :=
  Caller.private_descriptionFits layout zeroValid sampler scalar_fits (by change 2 + 1 < 4096; decide)
example : (scalarProgram.lower (Fresh.port layout)).DescriptionFits :=
  Caller.scalar_descriptionFits layout zeroValid sampler scalar_fits (by change 2 < 4096; decide)
example : WordIO.NamesAccounted (privateProgram.lower (Fresh.port layout)) (Caller.nameSlots layout zeroValid 127 3) :=
  Caller.private_names layout zeroValid sampler scalar_words scalar_names

private def saved : List (Schnorr.TapeCell Nat) := [(9, 0, 10), (1, 0, 0), (3, 0, 1)]
private def remaining : List (Schnorr.TapeCell Nat) := [(9, 0, 10), (1, 22, 0), (3, 0, 1)]
private def state : Schnorr.RawTape.State Nat := ⟨saved, remaining⟩
private def store : (Read.store layout).Value := ⟨Caller.rawScalar state, by
  change ((3 ≤ 6 ∧ ∀ cell ∈ saved, cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096) ∧ 3 < 6) ∧
    (3 ≤ 6 ∧ ∀ cell ∈ remaining, cell.1 < 4096 ∧ cell.2.1 < 4096 ∧ cell.2.2 < 4096)
  simp [saved, remaining]⟩
private def privateInput (range : Fin 4094) : (Caller.privateInput layout).Value :=
  ⟨Caller.rawPrivate range.val state, range.isLt, store.property⟩
private def empty : (Read.store layout).Value := ⟨([], []), by
  change ((0 ≤ 6 ∧ ∀ cell ∈ ([] : List (Schnorr.TapeCell Nat)), layout.entry.valid cell) ∧ 0 < 6) ∧
    (0 ≤ 6 ∧ ∀ cell ∈ ([] : List (Schnorr.TapeCell Nat)), layout.entry.valid cell)
  simp⟩

example : ¬ (Caller.privateInput layout).valid (Caller.rawPrivate 4094 state) := by
  intro valid
  have impossible : 4094 < 4094 := valid.1
  omega

private def run {A B : Type} (input : Layout 12 A) (output : Layout 12 B)
    (code : Interactive.Code 12) (value : input.Value) (replies : List (Word 12)) := do
  let initial := input.representation.initial value
  let before := { initial with bufs := fun b => if b = 200 then #[77] else initial.bufs b
                               caps := fun b => if b = 200 then 4 else initial.caps b
                               regs := fun r => if r = 99 then 91 else initial.regs r
                               tapePos := 9 }
  let result ← WordIO.run .unit RandomTape.zero 100000 (code.lower (Fresh.port layout)) before replies
  pure ((output.representation.encoding.decode (result.state.bufs 0).toList).map Subtype.val,
    result.trace, result.remaining, result.state.bufs 200, result.state.caps 200, result.state.regs 99,
    result.state.tapePos, (List.range 12).all (fun i => result.state.caps (i + 1) == 0))
private def runPrivate (range : Fin 4094) := run (Caller.privateInput layout) (Reply.privateOutput layout) privateProgram (privateInput range)
private def runScalar := run (Read.store layout) (Reply.scalarOutput layout) scalarProgram

open Lean in
run_cmd do
  -- The saved natural 10 is oversized for range 7, so the actual decoder must return 2.
  unless runPrivate 7 [88] == some (some (7, 2, saved, [(1, 22, 0), (3, 0, 1)]), [],
      [88], #[77], 4, 91, 9, true) do
    throwError "complete private hit lost the retained range, skipped remainder, or consumed randomness"
  unless runPrivate 1 [88] == some (some (1, 1, saved, [(9, 0, 10), (1, 22, 0)]), [],
      [88], #[77], 4, 91, 9, true) do
    throwError "complete private hit changed another family"
  for (range, answer, tag) in [((0 : Fin 4094), (0 : Word 12), (2 : Nat)), (4093, 4093, 4095)] do
    let rangeWord := BitVec.ofNat 12 range.val
    unless runPrivate range [rangeWord, answer, 88] ==
        some (some (range.val, answer.toNat, saved ++ [(tag, 0, answer.toNat)], remaining),
          [.output rangeWord, .invoke, .input rangeWord, .input answer], [88], #[77], 4, 91, 9, true) do
      throwError "complete private miss built the wrong tag, forwarded the wrong range, or lost the reply"
  unless runScalar store [88] == some (some (22, saved, [(9, 0, 10), (3, 0, 1)]), [],
      [88], #[77], 4, 91, 9, true) do
    throwError "complete challenge hit returned the wrong scalar or changed private replay cells"
  for answer in [(0 : Word 12), 99, 4095] do
    unless runScalar empty [4095, answer, 88] == some (some (answer.toNat, [(1, answer.toNat, 0)], []),
        [.output 4095, .invoke, .input 4095, .input answer], [88], #[77], 4, 91, 9, true) do
      throwError "complete challenge miss failed to construct and decode the scalar reply"
  unless runPrivate 0 [] == none do throwError "complete private miss succeeded without an oracle reply"
  unless runScalar empty [] == none do throwError "complete challenge miss succeeded without an oracle reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Constructed.addLiteral, ``Caller.private_refines, ``Caller.scalar_refines,
      ``Caller.private_source, ``Caller.scalar_source, ``Caller.private_observe, ``Caller.scalar_observe,
      ``Caller.private_time, ``Caller.scalar_time, ``Caller.private_words, ``Caller.scalar_words,
      ``Caller.private_descriptionFits, ``Caller.scalar_descriptionFits,
      ``Caller.private_resources, ``Caller.scalar_resources, ``private_bounded, ``scalar_bounded,
      ``scalar_correct, ``scalar_words] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrROMTapeCaller
