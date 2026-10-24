import Proofs.Runtime.Caliper.SchnorrAGMHandlerHashMemory
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMHandlerHash
open CaliperBackend.SchnorrAGM.Handler.HashComponent

private def scheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def layout : CaliperBackend.SchnorrAGM.Handler.Layouts 16 Nat (Word 16) (Word 16) 1 1 65535 where
  scheme := scheme
  groups := 3
  rows := 3
  coefficients := 5
  rangeFits := by decide
  counterFits := by decide
  groupCountFits := by decide
  rowCountFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide

private def mul : Implementation .unit scheme.affine scheme.scalar (fun value => value.1 * value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .mul (by decide)).viewInput scheme.affine.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput scheme.scalar.representation
      (fun value => ⟨value.val.1 * value.val.2, trivial⟩) (fun _ => rfl)
private def add : Implementation .unit scheme.affine scheme.scalar (fun value => value.1 + value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit .add (by decide)).viewInput scheme.affine.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput scheme.scalar.representation
      (fun value => ⟨value.val.1 + value.val.2, trivial⟩) (fun _ => rfl)
private theorem mulBound : mul.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem addBound : add.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem mulNames : NamesBound mul.program.code 3 := ⟨by decide, by decide⟩
private theorem addNames : NamesBound add.program.code 3 := ⟨by decide, by decide⟩

private def sampleSpec : OracleSpec Unit := fun _ => scheme.scalar.Value
private def replyView : (Σ _ : (PairSampling.input 16).Value, scheme.scalar.Value) ≃ scheme.scalar.Value where
  toFun := Sigma.snd
  invFun value := ⟨⟨(), trivial⟩, value⟩
  left_inv value := by rcases value with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 16 sampleSpec where
  Request := (PairSampling.input 16).Value
  source _ := ()
  request := (PairSampling.input 16).representation
  reply := scheme.scalar.representation.transport replyView
private def sampleSource : OracleComp sampleSpec scheme.scalar.Value := queryBind () Pure.pure
private def sampler : Interactive.Code 16 := .query
private theorem sampleCorrect : Interactive.Refines port .unit (PairSampling.input 16).representation
    scheme.scalar.representation (fun _ => sampleSource) sampler := by
  have projected := (Interactive.Refines.query port .unit).viewOutput scheme.scalar.representation
    (fun packet => packet.2) (fun _ => rfl)
  convert projected using 1 <;> rfl
private theorem sampleTime : Interactive.TimeBound port .unit (PairSampling.input 16).representation sampler 4 :=
  Interactive.TimeBound.query
private theorem sampleWords : (sampler.lower port).descriptionWords ≤ 20 := by decide
private theorem sampleNames : WordIO.NamesBound (sampler.lower port) 3 := ⟨by decide, by decide⟩
private theorem sampleFits : (sampler.lower port).DescriptionFits :=
  WordIO.exchange_descriptionFits 0 1 (by decide) (by decide)

private def program := code layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler
private theorem refined : Interactive.Refines port .unit layout.hashInput.representation layout.scalarOutput.representation
    (source layout trivial mul add mulNames.buffers addNames.buffers (by decide) sampleSource) program :=
  refines layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampleCorrect
private theorem timed : Interactive.TimeBound port .unit layout.hashInput.representation program (timeBudget layout 6 6 4) :=
  time_bound layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampleCorrect mulBound addBound sampleTime
private theorem stored : (program.lower port).descriptionWords ≤ codeBudget layout 27 27 20 :=
  code_bound layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler mulBound addBound sampleWords
private theorem accepted : (program.lower port).DescriptionFits :=
  descriptionFits layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler
    sampleFits addNames sampleNames (by decide)
private theorem boundedBuffers : (program.lower port).memBound ≤ 12 :=
  buffers layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler addNames sampleNames
private theorem named : WordIO.NamesAccounted (program.lower port) 6 :=
  names (slots := 3) (sampleSlots := 3) layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler mulNames addNames sampleNames

private theorem valid_iff (g pk : Word 16) (message : Nat) (groups : List (Word 16)) (rows : List (List (Word 16)))
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    layout.hashInput.valid ((message, groups, rows), (g, pk), entries, basis, signed, malformed, bad) ↔
      (message < 256 ∧ groups.length ≤ 3 ∧ (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 5) ∧
        (entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 3 ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256)) ∧
        layout.hash.admissible (message, groups, rows, entries, basis, signed, malformed, bad) := by
  change (((message < 256 ∧ (groups.length ≤ 3 ∧ ∀ _ ∈ groups, True) ∧
    (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 5 ∧ ∀ _ ∈ row, True)) ∧ (True ∧ True) ∧
    (entries.length ≤ 3 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 3 ∧ ∀ _ ∈ basis, True ∧ True) ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _) ↔ _
  simp only [and_true, true_and, implies_true, and_assoc]
  rfl

private def full : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)) :=
  [((3, 4), (0, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, true, 13, 14))]
private def duplicate (g pk : Word 16) : layout.hashInput.Value :=
  ⟨((3, [4], [[2, 3, 4]]), (g, pk), full, [(1, 0), (0, 1), (5, 7)], [9], true, false), by rw [valid_iff]; decide⟩
private def miss (g pk : Word 16) : layout.hashInput.Value :=
  ⟨((3, [4], [[2, 3, 4]]), (g, pk), [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1), (5, 7)], [9], false, false), by rw [valid_iff]; decide⟩
private def refused (g pk : Word 16) (groups : List (Word 16)) (rows : List (List (Word 16))) (bad : Bool)
    (valid : layout.hashInput.valid ((3, groups, rows), (g, pk), full, [(1, 0), (0, 1), (5, 7)], [9], false, bad)) : layout.hashInput.Value :=
  ⟨((3, groups, rows), (g, pk), full, [(1, 0), (0, 1), (5, 7)], [9], false, bad), valid⟩

example : ¬ layout.hashInput.valid ((3, [7], [[2]]), (9, 10), full, [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.hashInput.valid ((256, [], []), (9, 10), [], [], [], false, false) := by rw [valid_iff]; decide

private def execute (request : layout.hashInput.Value) (replies : List (Word 16)) := do
  let initial := layout.hashInput.representation.initial request
  let before := { initial with
    regs := fun r => if r = 200 then 99 else initial.regs r
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (program.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200,
    result.state.caps 200, result.state.regs 200, result.state.tapePos,
    (List.range 30).all (fun i => result.state.caps (i + 1) == 0), decide (result.time ≤ timeBudget layout 6 6 4))

open Lean in
run_cmd do
  let check := fun input replies bytes trace remaining =>
    execute input replies == some (bytes, trace, remaining, #[77], 4, 99, 7, true, true)
  for (g, pk) in ([(9, 10), (65535, 0)] : List (Word 16 × Word 16)) do
    unless check (duplicate g pk) [88]
        #[0, 0, 0, g, pk, 3, 3, 4, 0, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
          3, 1, 0, 0, 1, 5, 7, 1, 9, 1, 0] [] [88] do
      throwError "common-store hash lost runtime configuration, cached zero/first entry, empty reply, state or frame"
    unless check (miss g pk) [9, 88]
        (#[9, 0, 0, g, pk, 2, 3, 4, 9, 1, 22, 31, 5, 6, 1, 1, 13, 14] ++ Array.replicate 6 0 ++
          #[3, 1, 0, 0, 1, 5, 7, 1, 9, 0, 0]) [.invoke, .input 9] [88] do
      throwError "common-store hash miss lost its sample, flattened coefficients, configuration or updated cache"
    let rejected := fun bad =>
      #[0, 0, 0, g, pk, 3, 3, 4, 0, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
        3, 1, 0, 0, 1, 5, 7, 1, 9, 1, bad]
    unless check (refused g pk [] [] false (by rw [valid_iff]; decide)) [88] (rejected 0) [] [88] do
      throwError "common-store malformed hash sampled or required a free store slot"
    unless check (refused g pk [4] [[2], [3]] false (by rw [valid_iff]; decide)) [] (rejected 0) [] [] do
      throwError "common-store hash accepted multiple rows or failed without oracle input on rejection"
    unless check (refused g pk [4, 7, 9] [[2, 3, 4, 5, 6], [], [7]] true (by rw [valid_iff]; decide)) [] (rejected 1) [] [] do
      throwError "common-store hash lost configuration, bad flag or histories on a full malformed request"
    unless execute (miss g pk) [] == none do
      throwError "common-store hash miss succeeded without its challenge reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``prepare, ``finish, ``refines, ``erase, ``reply_config, ``time_bound, ``code_bound, ``names,
      ``buffers, ``descriptionFits, ``resources, ``source_original, ``input_valid, ``reserved_input,
      ``refined, ``timed, ``stored, ``accepted, ``boundedBuffers, ``named] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMHandlerHash
