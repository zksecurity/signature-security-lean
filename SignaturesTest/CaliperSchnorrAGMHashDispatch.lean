import Proofs.Runtime.Caliper.SchnorrAGMHashDispatchMemory
import Proofs.Runtime.Caliper.SchnorrAGMExtractionMemory
import Proofs.Runtime.Caliper.SchnorrAGMCallerFinishBounds
import Proofs.Runtime.Caliper.SchnorrAGMCallerFinishSource
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMHashDispatch

-- Modular-word arithmetic tests the executed wiring. The generic source
-- theorem separately covers field arithmetic and the uniform challenge law.
private def scheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def hash : CaliperBackend.SchnorrAGM.Hash.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scheme := scheme
  coefficients := 5
  counterFits := by decide
  coefficientCountFits := by decide
  storageFits := by decide

private def layout : CaliperBackend.SchnorrAGM.HashDispatch.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  hash := hash
  groups := 3
  rows := 3
  groupCountFits := by decide
  rowCountFits := by decide
  storageFits := by decide

private def binary (op : BinOp) : Implementation .unit scheme.affine scheme.scalar (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op (by decide)).viewInput scheme.affine.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput scheme.scalar.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)
private def mul : Implementation .unit scheme.affine scheme.scalar (fun value => value.1 * value.2) := binary .mul
private def add : Implementation .unit scheme.affine scheme.scalar (fun value => value.1 + value.2) := binary .add
private def sub : Implementation .unit scheme.affine scheme.scalar (fun value => value.1 - value.2) := binary .sub
private def divide : Implementation .unit scheme.affine scheme.scalar (fun value => value.1 / value.2) := binary .udiv
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem divBound : divide.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem subNames : NamesBound sub.program.code 3 := ⟨by decide, by decide⟩
private theorem divNames : NamesBound divide.program.code 3 := ⟨by decide, by decide⟩
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

private def program := CaliperBackend.SchnorrAGM.HashDispatch.code layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler
private theorem refined : Interactive.Refines port .unit layout.input.representation
    (CaliperBackend.SchnorrAGM.Read.output scheme).representation
    (CaliperBackend.SchnorrAGM.HashDispatch.source layout trivial mul add mulNames.buffers addNames.buffers (by decide) sampleSource) program :=
  CaliperBackend.SchnorrAGM.HashDispatch.refines layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampleCorrect
private theorem timed : Interactive.TimeBound port .unit layout.input.representation program
    (CaliperBackend.SchnorrAGM.HashDispatch.timeBudget layout 6 6 4) :=
  CaliperBackend.SchnorrAGM.HashDispatch.time_bound layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampleCorrect
    mulBound addBound sampleTime
private theorem stored : (program.lower port).descriptionWords ≤ CaliperBackend.SchnorrAGM.HashDispatch.codeBudget layout 27 27 20 :=
  CaliperBackend.SchnorrAGM.HashDispatch.code_bound layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler
    mulBound addBound sampleWords
private theorem accepted : (program.lower port).DescriptionFits :=
  CaliperBackend.SchnorrAGM.HashDispatch.descriptionFits layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler
    sampleFits addNames sampleNames (by decide)
private theorem buffers : (program.lower port).memBound ≤ 11 :=
  CaliperBackend.SchnorrAGM.HashDispatch.buffers layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler addNames sampleNames

private def extractionProgram := CaliperBackend.SchnorrAGM.Extraction.code layout trivial mul add sub divide
  mulNames.buffers addNames.buffers subNames.buffers divNames.buffers (by decide) port sampler
private theorem extractionRefined : Interactive.Refines port .unit (CaliperBackend.SchnorrAGM.Extraction.input layout).representation
    (CaliperBackend.SchnorrAGM.Read.output scheme).representation
    (CaliperBackend.SchnorrAGM.Extraction.source layout trivial mul add sub divide mulNames.buffers addNames.buffers subNames.buffers (by decide) sampleSource) extractionProgram :=
  CaliperBackend.SchnorrAGM.Extraction.refines layout trivial mul add sub divide mulNames.buffers addNames.buffers subNames.buffers divNames.buffers (by decide) port sampleCorrect
private theorem extractionTimed : Interactive.TimeBound port .unit (CaliperBackend.SchnorrAGM.Extraction.input layout).representation extractionProgram
    (CaliperBackend.SchnorrAGM.Extraction.timeBudget layout 6 6 6 6 4) :=
  CaliperBackend.SchnorrAGM.Extraction.time_bound layout trivial mul add sub divide mulNames.buffers addNames.buffers subNames.buffers divNames.buffers (by decide)
    mulBound addBound subBound divBound port sampleCorrect sampleTime
private theorem extractionStored : (extractionProgram.lower port).descriptionWords ≤ CaliperBackend.SchnorrAGM.Extraction.codeBudget layout 27 27 27 27 20 :=
  CaliperBackend.SchnorrAGM.Extraction.code_bound layout trivial mul add sub divide mulNames.buffers addNames.buffers subNames.buffers divNames.buffers (by decide)
    mulBound addBound subBound divBound port sampleWords
private theorem extractionAccepted : (extractionProgram.lower port).DescriptionFits :=
  CaliperBackend.SchnorrAGM.Extraction.descriptionFits layout trivial mul add sub divide mulNames.buffers addNames.buffers subNames.buffers divNames.buffers (by decide)
    port sampleFits addNames sampleNames (by decide)

private theorem valid_iff (message : Nat) (groups : List (Word 16)) (rows : List (List (Word 16)))
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    layout.input.valid (message, groups, rows, entries, basis, signed, malformed, bad) ↔
      (message < 256 ∧ groups.length ≤ 3 ∧ (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 5) ∧
        (entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 3 ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256)) ∧
        layout.admissible (message, groups, rows, entries, basis, signed, malformed, bad) := by
  change ((message < 256 ∧ (groups.length ≤ 3 ∧ ∀ group ∈ groups, True) ∧
    (rows.length ≤ 3 ∧ ∀ row ∈ rows, row.length ≤ 5 ∧ ∀ coefficient ∈ row, True) ∧
    (entries.length ≤ 3 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 3 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _) ↔ _
  simp only [and_true, implies_true]

private def full : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)) :=
  [((3, 4), (2, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, true, 13, 14))]
private def duplicate : layout.input.Value :=
  ⟨(3, [4], [[2, 3, 4]], full, [(1, 0), (0, 1), (5, 7)], [9], true, false), by rw [valid_iff]; decide⟩
private def miss : layout.input.Value :=
  ⟨(3, [4], [[2, 3, 4]], [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1), (5, 7)], [9], false, false), by rw [valid_iff]; decide⟩
private def refused (groups : List (Word 16)) (rows : List (List (Word 16))) (bad : Bool)
    (valid : layout.input.valid (3, groups, rows, full, [(1, 0), (0, 1), (5, 7)], [9], false, bad)) : layout.input.Value :=
  ⟨(3, groups, rows, full, [(1, 0), (0, 1), (5, 7)], [9], false, bad), valid⟩

example : ¬ layout.input.valid (3, [7], [[2]], full, [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid (256, [], [], [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid (3, List.replicate 4 0, [], [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid (3, [], List.replicate 4 [], [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid (3, [], [List.replicate 6 0], [], [], [], false, false) := by rw [valid_iff]; decide

private theorem memory (tape : RandomTape 16) (value : layout.input.Value) (before : State 16)
    (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (program.execute port .unit tape before)) :
    finished.time ≤ CaliperBackend.SchnorrAGM.HashDispatch.timeBudget layout 6 6 4 ∧
      ∃ answer ∈ support (CaliperBackend.SchnorrAGM.HashDispatch.source layout trivial mul add mulNames.buffers addNames.buffers (by decide) sampleSource value),
        (CaliperBackend.SchnorrAGM.Read.output scheme).representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape (program.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            ((program.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (program.lower port).memBound) ≤
              5 * CaliperBackend.SchnorrAGM.HashDispatch.codeBudget layout 27 27 20 + 24 + registers + 3 * buffers + before.liveMem buffers +
                CaliperBackend.SchnorrAGM.HashDispatch.timeBudget layout 6 6 4 := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    CaliperBackend.SchnorrAGM.HashDispatch.resources layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampleCorrect
      mulBound addBound sampleTime sampleWords mulNames addNames sampleNames tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private theorem extractionMemory (tape : RandomTape 16) (value : (CaliperBackend.SchnorrAGM.Extraction.input layout).Value) (before : State 16)
    (holds : (CaliperBackend.SchnorrAGM.Extraction.input layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (extractionProgram.execute port .unit tape before)) :
    finished.time ≤ CaliperBackend.SchnorrAGM.Extraction.timeBudget layout 6 6 6 6 4 ∧
      ∃ answer ∈ support (CaliperBackend.SchnorrAGM.Extraction.source layout trivial mul add sub divide mulNames.buffers addNames.buffers subNames.buffers (by decide) sampleSource value),
        (CaliperBackend.SchnorrAGM.Read.output scheme).representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape (extractionProgram.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            ((extractionProgram.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (extractionProgram.lower port).memBound) ≤
              5 * CaliperBackend.SchnorrAGM.Extraction.codeBudget layout 27 27 27 27 20 + 24 + registers + 3 * buffers + before.liveMem buffers +
                CaliperBackend.SchnorrAGM.Extraction.timeBudget layout 6 6 6 6 4 := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    CaliperBackend.SchnorrAGM.Extraction.resources layout trivial mul add sub divide mulNames.buffers addNames.buffers subNames.buffers divNames.buffers (by decide) port sampleCorrect
      mulBound addBound subBound divBound sampleTime sampleWords mulNames addNames subNames.accounted divNames.accounted sampleNames tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def executeProgram (body : Interactive.Code 16) (budget : Nat) (initial : State 16) (replies : List (Word 16)) := do
  let before := { initial with
    regs := fun r => if r = 200 then 99 else initial.regs r
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (body.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200,
    result.state.caps 200, result.state.regs 200, result.state.tapePos,
    (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ budget))

private def execute (request : layout.input.Value) (replies : List (Word 16)) :=
  executeProgram program (CaliperBackend.SchnorrAGM.HashDispatch.timeBudget layout 6 6 4)
    (layout.input.representation.initial request) replies
private def executeExtraction (request : layout.input.Value) (response : Word 16) (replies : List (Word 16)) :=
  executeProgram extractionProgram (CaliperBackend.SchnorrAGM.Extraction.timeBudget layout 6 6 6 6 4)
    ((CaliperBackend.SchnorrAGM.Extraction.input layout).representation.initial ⟨(request.val, response), request.property, trivial⟩) replies

-- Independent zero-capacity lists exercise rejection when neither singleton
-- branch can be represented; no cache room is required for the full table.
private def emptyLayout : CaliperBackend.SchnorrAGM.HashDispatch.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  hash := hash
  groups := 0
  rows := 0
  groupCountFits := by decide
  rowCountFits := by decide
  storageFits := by decide
private def emptyRequest : (CaliperBackend.SchnorrAGM.Extraction.input emptyLayout).Value :=
  ⟨((3, [], [], full, [(1, 0), (0, 1), (5, 7)], [9], false, true), 73), by
    refine ⟨⟨⟨by change 3 < 256; decide, ⟨by decide, by simp⟩, ⟨by decide, by simp⟩, ?_⟩, trivial⟩, trivial⟩
    exact (refused [] [] true (by rw [valid_iff]; decide)).property.1.2.2.2⟩
private def emptyProgram := CaliperBackend.SchnorrAGM.Extraction.code emptyLayout trivial mul add sub divide
  mulNames.buffers addNames.buffers subNames.buffers divNames.buffers (by decide) port sampler

open CaliperBackend.SchnorrAGM in
private def finishPacket {P : Type} (request : layout.input.Value) (response : Word 16) : CallerFinish.Packet layout P :=
  (.inl ⟨((request.val.1, response), request.val.2.1, request.val.2.2.1),
    ⟨request.property.1.1, trivial⟩, request.property.1.2.1, request.property.1.2.2.1⟩,
    ⟨((20, 31), request.val.2.2.2), ⟨trivial, trivial⟩, request.property.1.2.2.2⟩)
open CaliperBackend.SchnorrAGM in
private theorem finishReady {P : Type} (request : layout.input.Value) (response : Word 16) :
    CallerFinish.ready layout (finishPacket (P := P) request response) := request.property.2

open CaliperBackend.SchnorrAGM in
private def executeFinish {P : Type} (pending : Representation 16 P)
    (fits : 1 + max (CallerFinish.forgery layout).representation.encoding.words pending.encoding.words + scheme.store.representation.encoding.words < 2 ^ 16)
    (packet : CallerFinish.Packet layout P) (replies : List (Word 16)) :=
  executeProgram (CallerFinish.code layout pending fits ⟨0, trivial⟩ extractionProgram)
    (CallerFinish.timeBudget layout pending fits (Extraction.timeBudget layout 6 6 6 6 4))
    ((CallerFinish.input layout pending fits).initial packet) replies

open CaliperBackend.SchnorrAGM in
private def finishProgram := CallerFinish.code layout scheme.scalar.representation (by decide) ⟨0, trivial⟩ extractionProgram
open CaliperBackend.SchnorrAGM in
private theorem finishRefined : Interactive.RefinesOn (CallerFinish.ready layout) port .unit
    (CallerFinish.input layout scheme.scalar.representation (by decide)) scheme.scalar.representation
    (CallerFinish.denote layout ⟨0, trivial⟩ (Extraction.source layout trivial mul add sub divide
      mulNames.buffers addNames.buffers subNames.buffers (by decide) sampleSource)) finishProgram :=
  CallerFinish.refines layout scheme.scalar.representation (by decide) port extractionRefined ⟨0, trivial⟩
open CaliperBackend.SchnorrAGM in
private theorem finishTimed : Interactive.TimeBoundOn (CallerFinish.ready layout) port .unit
    (CallerFinish.input layout scheme.scalar.representation (by decide)) finishProgram
    (CallerFinish.timeBudget layout scheme.scalar.representation (by decide) (Extraction.timeBudget layout 6 6 6 6 4)) :=
  CallerFinish.time_bound layout scheme.scalar.representation (by decide) port extractionRefined extractionTimed ⟨0, trivial⟩
open CaliperBackend.SchnorrAGM in
private theorem finishStored : (finishProgram.lower port).descriptionWords ≤
    CallerFinish.codeBudget layout scheme.scalar.representation (by decide) (Extraction.codeBudget layout 27 27 27 27 20) :=
  CallerFinish.code_bound layout scheme.scalar.representation (by decide) port extractionStored ⟨0, trivial⟩
open CaliperBackend.SchnorrAGM in
private theorem finishFits : (finishProgram.lower port).DescriptionFits :=
  CallerFinish.descriptionFits layout scheme.scalar.representation (by decide) port ⟨0, trivial⟩ extractionAccepted

open Lean in
run_cmd do
  let check := fun input replies bytes trace remaining =>
    execute input replies == some (bytes, trace, remaining, #[77], 4, 99, 7, true, true)
  unless check duplicate [88]
      #[2, 3, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
        3, 1, 0, 0, 1, 5, 7, 1, 9, 1, 0] [] [88] do
    throwError "accepted singleton request failed to retain the first cached challenge without sampling"
  unless check miss [9, 88]
      (#[9, 2, 3, 4, 9, 1, 22, 31, 5, 6, 1, 1, 13, 14] ++ Array.replicate 6 0 ++
        #[3, 1, 0, 0, 1, 5, 7, 1, 9, 0, 0]) [.invoke, .input 9] [88] do
    throwError "accepted singleton request failed to route runtime coefficients and original state"
  let rejected := fun bad =>
    #[0, 3, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
      3, 1, 0, 0, 1, 5, 7, 1, 9, 1, bad]
  unless check (refused [] [] false (by rw [valid_iff]; decide)) [88] (rejected 0) [] [88] do
    throwError "empty request sampled or did not set malformed while preserving the full cache"
  unless check (refused [] [[2, 3, 4]] false (by rw [valid_iff]; decide)) [88] (rejected 0) [] [88] do
    throwError "missing point was accepted despite a singleton coefficient row"
  unless check (refused [4, 7] [[2, 3, 4]] false (by rw [valid_iff]; decide)) [88] (rejected 0) [] [88] do
    throwError "multiple points were accepted or sampled"
  unless check (refused [4] [] false (by rw [valid_iff]; decide)) [88] (rejected 0) [] [88] do
    throwError "missing coefficient row was accepted despite a singleton point"
  unless check (refused [4] [[2], [3]] false (by rw [valid_iff]; decide)) [88] (rejected 0) [] [88] do
    throwError "multiple coefficient rows were accepted or sampled"
  unless check (refused [4, 7, 9] [[2, 3, 4, 5, 6], [], [7]] true (by rw [valid_iff]; decide)) [] (rejected 1) [] [] do
    throwError "largest malformed request needed a random reply, lost bad, or overwrote histories"
  unless execute miss [] == none do
    throwError "accepted fresh request succeeded without its challenge reply"
  let terminalCheck := fun request response replies bytes trace remaining =>
    executeExtraction request response replies == some (bytes, trace, remaining, #[77], 4, 99, 7, true, true)
  unless terminalCheck duplicate 33 [88]
      #[2, 3, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
        3, 1, 0, 0, 1, 5, 7, 1, 9, 1, 0] [] [88] do
    throwError "terminal did not use the first cached explanation or preserve response and state"
  let missState := #[2, 3, 4, 9, 1, 22, 31, 5, 6, 1, 1, 13, 14] ++ Array.replicate 6 0 ++
    #[3, 1, 0, 0, 1, 5, 7, 1, 9, 0, 0]
  unless terminalCheck miss 102 [9, 88] (#[2] ++ missState) [.invoke, .input 9] [88] do
    throwError "terminal did not flatten coefficients, sample once, and compute the quotient"
  unless terminalCheck miss 142 [9, 88] (#[3] ++ missState) [.invoke, .input 9] [88] do
    throwError "terminal failed to use its runtime response scalar"
  let terminalRejected := fun malformed bad =>
    #[0, 3, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
      3, 1, 0, 0, 1, 5, 7, 1, 9, malformed, bad]
  let malformedInputs := [
    refused [] [] false (by rw [valid_iff]; decide),
    refused [] [[2, 3, 4]] false (by rw [valid_iff]; decide),
    refused [4, 7] [[2, 3, 4]] false (by rw [valid_iff]; decide),
    refused [4] [] false (by rw [valid_iff]; decide),
    refused [4] [[2], [3]] false (by rw [valid_iff]; decide)]
  for value in malformedInputs do
    unless terminalCheck value 73 [88] (terminalRejected 0 0) [] [88] do
      throwError "malformed final forgery sampled, changed state, or returned a nonzero scalar"
  unless terminalCheck (refused [4, 7, 9] [[2, 3, 4, 5, 6], [], [7]] true (by rw [valid_iff]; decide))
      73 [] (terminalRejected 0 1) [] [] do
    throwError "largest malformed final forgery lost the bad flag or needed randomness"
  let flagged : layout.input.Value := ⟨(3, [], [], full, [(1, 0), (0, 1), (5, 7)], [9], true, true), by rw [valid_iff]; decide⟩
  unless terminalCheck flagged 73 [] (terminalRejected 1 1) [] [] do
    throwError "malformed final forgery reset a preexisting flag"
  unless executeProgram emptyProgram (CaliperBackend.SchnorrAGM.Extraction.timeBudget emptyLayout 6 6 6 6 4)
      ((CaliperBackend.SchnorrAGM.Extraction.input emptyLayout).representation.initial emptyRequest) [] ==
        some (terminalRejected 0 1, [], [], #[77], 4, 99, 7, true, true) do
    throwError "zero-capacity final-forgery lists failed to reject while preserving a full cache"
  unless executeExtraction miss 102 [] == none do
    throwError "fresh final forgery succeeded without its required challenge"
  let finishCheck := fun request response replies scalar trace remaining =>
    executeFinish scheme.scalar.representation (by decide) (finishPacket request response) replies ==
      some (#[scalar], trace, remaining, #[77], 4, 99, 7, true, true) &&
    executeFinish scheme.state.representation (by decide) (finishPacket request response) replies ==
      some (#[scalar], trace, remaining, #[77], 4, 99, 7, true, true)
  unless finishCheck duplicate 33 [88] 2 [] [88] do
    throwError "caller return routing failed across a padded forgery or pending branch"
  unless finishCheck miss 142 [9, 88] 3 [.invoke, .input 9] [88] do
    throwError "caller return did not route the response, stored state or sampler through extraction"
  for value in malformedInputs do
    unless finishCheck value 73 [] 0 [] [] do
      throwError "malformed caller return failed after configuration and padding removal"
  let stored := (finishPacket (P := Word 16) duplicate 33).2
  unless executeFinish scheme.scalar.representation (by decide) (.inr ⟨77, trivial⟩, stored) [88] ==
      some (#[0], [], [88], #[77], 4, 99, 7, true, true) do
    throwError "padded cutoff invoked extraction, needed room, or failed to return stored zero"
  unless executeFinish scheme.state.representation (by decide) (.inr ⟨stored.val.2, stored.property.2⟩, stored) [] ==
      some (#[0], [], [], #[77], 4, 99, 7, true, true) do
    throwError "large pending cutoff sampled or failed to release its copied frame"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``ListBytes.singleton_bytes, ``CaliperBackend.SchnorrAGM.HashDispatch.test,
      ``CaliperBackend.SchnorrAGM.HashDispatch.selector, ``CaliperBackend.SchnorrAGM.HashDispatch.accept,
      ``CaliperBackend.SchnorrAGM.HashDispatch.reject, ``CaliperBackend.SchnorrAGM.HashDispatch.refines,
      ``CaliperBackend.SchnorrAGM.HashDispatch.source_original, ``CaliperBackend.SchnorrAGM.HashDispatch.source_no,
      ``CaliperBackend.SchnorrAGM.HashDispatch.reserved_input, ``CaliperBackend.SchnorrAGM.HashDispatch.time_bound,
      ``CaliperBackend.SchnorrAGM.HashDispatch.code_bound, ``CaliperBackend.SchnorrAGM.HashDispatch.names,
      ``CaliperBackend.SchnorrAGM.HashDispatch.buffers, ``CaliperBackend.SchnorrAGM.HashDispatch.descriptionFits,
      ``CaliperBackend.SchnorrAGM.HashDispatch.resources, ``refined, ``timed, ``stored, ``accepted, ``buffers, ``memory,
      ``CaliperBackend.SchnorrAGM.ExtractionEntry.refines, ``CaliperBackend.SchnorrAGM.ExtractionEntry.time_bound,
      ``CaliperBackend.SchnorrAGM.ExtractionEntry.code_bound, ``CaliperBackend.SchnorrAGM.ExtractionEntry.descriptionFits,
      ``CaliperBackend.SchnorrAGM.Extraction.refines, ``CaliperBackend.SchnorrAGM.Extraction.source_original,
      ``CaliperBackend.SchnorrAGM.Extraction.source_no, ``CaliperBackend.SchnorrAGM.Extraction.reserved_input,
      ``CaliperBackend.SchnorrAGM.Extraction.time_bound, ``CaliperBackend.SchnorrAGM.Extraction.code_bound,
      ``CaliperBackend.SchnorrAGM.Extraction.names, ``CaliperBackend.SchnorrAGM.Extraction.descriptionFits,
      ``CaliperBackend.SchnorrAGM.Extraction.resources, ``extractionRefined, ``extractionTimed, ``extractionStored, ``extractionAccepted, ``extractionMemory,
      ``CaliperBackend.SchnorrAGM.CallerFinish.route, ``CaliperBackend.SchnorrAGM.CallerFinish.route_time,
      ``CaliperBackend.SchnorrAGM.CallerFinish.route_words, ``CaliperBackend.SchnorrAGM.CallerFinish.refines,
      ``CaliperBackend.SchnorrAGM.CallerFinish.success_original, ``CaliperBackend.SchnorrAGM.CallerFinish.time_bound,
      ``CaliperBackend.SchnorrAGM.CallerFinish.code_bound, ``CaliperBackend.SchnorrAGM.CallerFinish.names,
      ``CaliperBackend.SchnorrAGM.CallerFinish.descriptionFits, ``CaliperBackend.SchnorrAGM.CallerFinish.resources,
      ``finishReady, ``finishRefined, ``finishTimed, ``finishStored, ``finishFits] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMHashDispatch
