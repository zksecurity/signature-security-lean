import Proofs.Runtime.Caliper.SchnorrAGMReadMemory
import Proofs.Runtime.Caliper.SchnorrAGMExtractionReadMemory
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMRead

-- Executed word arithmetic is a wiring fixture, not a cryptographic field
-- implementation. Generic source theorems separately cover fields; in this
-- fixture unsigned division by zero returns zero.
private def layout : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def binary (op : BinOp) : Implementation .unit layout.affine layout.scalar (fun value => op.eval value.1 value.2) where
  preserves _ _ := trivial
  program := ((WordBinary.realizer .unit op (by decide)).viewInput layout.affine.representation
    (fun value => value.val) (fun _ => rfl)).viewOutput layout.scalar.representation
      (fun value => ⟨op.eval value.val.1 value.val.2, trivial⟩) (fun _ => rfl)
private def add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2) := binary .add
private def sub : Implementation .unit layout.affine layout.scalar (fun value => value.1 - value.2) := binary .sub
private def divide : Implementation .unit layout.affine layout.scalar (fun value => value.1 / value.2) := binary .udiv
private theorem subBound : sub.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem divBound : divide.BoundedBy 6 27 := ⟨fun _ => le_rfl, by decide⟩
private theorem subNames : NamesBound sub.program.code 3 := ⟨by decide, by decide⟩
private theorem divNames : NamesBound divide.program.code 3 := ⟨by decide, by decide⟩
private theorem addBound : add.BoundedBy 6 27 := ⟨fun _ => by change 6 ≤ 6; omega, by decide⟩
private theorem addNames : NamesBound add.program.code 3 := ⟨by decide, by decide⟩

private def sampleSpec : OracleSpec Unit := fun _ => layout.scalar.Value
private def replyView : (Σ _ : (PairSampling.input 16).Value, layout.scalar.Value) ≃ layout.scalar.Value where
  toFun := Sigma.snd
  invFun value := ⟨⟨(), trivial⟩, value⟩
  left_inv value := by rcases value with ⟨⟨position, valid⟩, answer⟩; cases position; rfl
  right_inv _ := rfl
private def port : Interactive.Port 16 sampleSpec where
  Request := (PairSampling.input 16).Value
  source _ := ()
  request := (PairSampling.input 16).representation
  reply := layout.scalar.representation.transport replyView
private def sampleSource : OracleComp sampleSpec layout.scalar.Value := queryBind () Pure.pure
private def sampler : Interactive.Code 16 := .query
private theorem sampleCorrect : Interactive.Refines port .unit (PairSampling.input 16).representation
    layout.scalar.representation (fun _ => sampleSource) sampler := by
  have projected := (Interactive.Refines.query port .unit).viewOutput layout.scalar.representation
    (fun packet => packet.2) (fun _ => rfl)
  convert projected using 1 <;> rfl
private theorem sampleTime : Interactive.TimeBound port .unit (PairSampling.input 16).representation sampler 4 :=
  Interactive.TimeBound.query
private theorem sampleWords : (sampler.lower port).descriptionWords ≤ 20 := by decide
private theorem sampleNames : WordIO.NamesBound (sampler.lower port) 3 := ⟨by decide, by decide⟩
private theorem sampleFits : (sampler.lower port).DescriptionFits :=
  WordIO.exchange_descriptionFits 0 1 (by decide) (by decide)

private def program := CaliperBackend.SchnorrAGM.Read.code layout trivial add addNames.buffers (by decide) port sampler
private theorem refined : Interactive.Refines port .unit (CaliperBackend.SchnorrAGM.Read.input layout).representation
    (CaliperBackend.SchnorrAGM.Read.output layout).representation
    (CaliperBackend.SchnorrAGM.Read.source layout trivial sampleSource) program :=
  CaliperBackend.SchnorrAGM.Read.refines layout trivial add addNames.buffers (by decide) port sampleCorrect
private theorem timed : Interactive.TimeBound port .unit (CaliperBackend.SchnorrAGM.Read.input layout).representation program
    (CaliperBackend.SchnorrAGM.Read.timeBudget layout 6 4) :=
  CaliperBackend.SchnorrAGM.Read.time_bound layout trivial add addNames.buffers (by decide) port sampleCorrect addBound.time_le sampleTime
private theorem stored : (program.lower port).descriptionWords ≤ CaliperBackend.SchnorrAGM.Read.codeBudget layout 27 20 :=
  CaliperBackend.SchnorrAGM.Read.code_bound layout trivial add addNames.buffers (by decide) port sampler addBound.code_le sampleWords
private theorem accepted : (program.lower port).DescriptionFits :=
  CaliperBackend.SchnorrAGM.Read.descriptionFits layout trivial add addNames.buffers (by decide) port sampler
    sampleFits addNames sampleNames (by decide)
private theorem buffers : (program.lower port).memBound ≤ 10 :=
  CaliperBackend.SchnorrAGM.Read.buffers layout trivial add addNames.buffers (by decide) port sampler addNames sampleNames

private def entryProgram := CaliperBackend.SchnorrAGM.EntryRead.code layout trivial add addNames.buffers (by decide) port sampler
private theorem entryRefined : Interactive.Refines port .unit (CaliperBackend.SchnorrAGM.Read.input layout).representation
    (CaliperBackend.SchnorrAGM.EntryRead.output layout).representation
    (CaliperBackend.SchnorrAGM.EntryRead.source layout trivial sampleSource) entryProgram :=
  CaliperBackend.SchnorrAGM.EntryRead.refines layout trivial add addNames.buffers (by decide) port sampleCorrect
private theorem entryTimed : Interactive.TimeBound port .unit (CaliperBackend.SchnorrAGM.Read.input layout).representation entryProgram
    (CaliperBackend.SchnorrAGM.EntryRead.timeBudget layout 6 4) :=
  CaliperBackend.SchnorrAGM.EntryRead.time_bound layout trivial add addNames.buffers (by decide) port sampleCorrect addBound.time_le sampleTime
private theorem entryStored : (entryProgram.lower port).descriptionWords ≤ CaliperBackend.SchnorrAGM.EntryRead.codeBudget layout 27 20 :=
  CaliperBackend.SchnorrAGM.EntryRead.code_bound layout trivial add addNames.buffers (by decide) port sampler addBound.code_le sampleWords
private theorem entryAccepted : (entryProgram.lower port).DescriptionFits :=
  CaliperBackend.SchnorrAGM.EntryRead.descriptionFits layout trivial add addNames.buffers (by decide) port sampler
    sampleFits addNames sampleNames (by decide)
private theorem entryBuffers : (entryProgram.lower port).memBound ≤ 10 :=
  CaliperBackend.SchnorrAGM.EntryRead.buffers layout trivial add addNames.buffers (by decide) port sampler addNames sampleNames

private def extractionProgram := CaliperBackend.SchnorrAGM.ExtractionRead.code layout trivial add sub divide
  addNames.buffers subNames.buffers divNames.buffers (by decide) port sampler
private theorem extractionRefined : Interactive.Refines port .unit (CaliperBackend.SchnorrAGM.ExtractionRead.input layout).representation
    (CaliperBackend.SchnorrAGM.Read.output layout).representation
    (CaliperBackend.SchnorrAGM.ExtractionRead.source layout trivial add sub divide addNames.buffers subNames.buffers (by decide) sampleSource) extractionProgram :=
  CaliperBackend.SchnorrAGM.ExtractionRead.refines layout trivial add sub divide addNames.buffers subNames.buffers divNames.buffers (by decide) port sampleCorrect
private theorem extractionTimed : Interactive.TimeBound port .unit (CaliperBackend.SchnorrAGM.ExtractionRead.input layout).representation extractionProgram
    (CaliperBackend.SchnorrAGM.ExtractionRead.timeBudget layout 6 6 6 4) :=
  CaliperBackend.SchnorrAGM.ExtractionRead.time_bound layout trivial add sub divide addNames.buffers subNames.buffers divNames.buffers (by decide)
    addBound subBound divBound port sampleCorrect sampleTime
private theorem extractionStored : (extractionProgram.lower port).descriptionWords ≤ CaliperBackend.SchnorrAGM.ExtractionRead.codeBudget layout 27 27 27 20 :=
  CaliperBackend.SchnorrAGM.ExtractionRead.code_bound layout trivial add sub divide addNames.buffers subNames.buffers divNames.buffers (by decide)
    addBound subBound divBound port sampleWords
private theorem extractionAccepted : (extractionProgram.lower port).DescriptionFits :=
  CaliperBackend.SchnorrAGM.ExtractionRead.descriptionFits layout trivial add sub divide addNames.buffers subNames.buffers divNames.buffers (by decide)
    port sampleFits addNames sampleNames (by decide)

private theorem valid_iff (key : Nat × Word 16) (affine : Word 16 × Word 16)
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    (CaliperBackend.SchnorrAGM.Read.input layout).valid (key, affine, entries, basis, signed, malformed, bad) ↔
      (key.1 < 256 ∧ (entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 3 ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256)) ∧
          ((lookupValue key (0, false, affine) entries).1 = false → entries.length ≤ 2) := by
  change (((key.1 < 256 ∧ True) ∧ (True ∧ True) ∧
    (entries.length ≤ 3 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 3 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _) ↔ _
  simp only [and_true, true_and, implies_true]
  rfl

private def full : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)) :=
  [((3, 4), (2, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, true, 13, 14))]
private def duplicate : (CaliperBackend.SchnorrAGM.Read.input layout).Value :=
  ⟨((3, 4), (5, 7), full, [(1, 0), (0, 1), (11, 13)], [9], true, false), by rw [valid_iff]; decide⟩
private def miss (bad : Bool) : (CaliperBackend.SchnorrAGM.Read.input layout).Value :=
  ⟨((3, 4), (5, 7), [((5, 6), (1, true, 13, 14))], [(1, 0), (0, 1), (11, 13)], [9], true, bad), by rw [valid_iff]; decide⟩
private def lastSlot : (CaliperBackend.SchnorrAGM.Read.input layout).Value :=
  ⟨((3, 4), (5, 7), [((5, 6), (1, true, 13, 14)), ((7, 8), (2, false, 0, 0))],
    [(1, 0), (0, 1), (11, 13)], [9], false, false), by rw [valid_iff]; decide⟩
private def changed : (CaliperBackend.SchnorrAGM.Read.input layout).Value :=
  ⟨((8, 12), (11, 13), [], [(2, 3)], [], false, false), by rw [valid_iff]; decide⟩

example : ¬ (CaliperBackend.SchnorrAGM.Read.input layout).valid
    ((7, 8), (5, 7), full, [(1, 0), (0, 1)], [], false, false) := by rw [valid_iff]; decide
example : ¬ (CaliperBackend.SchnorrAGM.Read.input layout).valid
    ((256, 8), (5, 7), [], [(1, 0), (0, 1)], [], false, false) := by rw [valid_iff]; decide

private theorem memory (tape : RandomTape 16) (value : (CaliperBackend.SchnorrAGM.Read.input layout).Value) (before : State 16)
    (holds : (CaliperBackend.SchnorrAGM.Read.input layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (program.execute port .unit tape before)) :
    finished.time ≤ CaliperBackend.SchnorrAGM.Read.timeBudget layout 6 4 ∧
      ∃ answer ∈ support (CaliperBackend.SchnorrAGM.Read.source layout trivial sampleSource value),
        (CaliperBackend.SchnorrAGM.Read.output layout).representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape (program.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            ((program.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (program.lower port).memBound) ≤
              5 * CaliperBackend.SchnorrAGM.Read.codeBudget layout 27 20 + 24 + registers + 3 * buffers + before.liveMem buffers +
                CaliperBackend.SchnorrAGM.Read.timeBudget layout 6 4 := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    CaliperBackend.SchnorrAGM.Read.resources layout trivial add addNames.buffers (by decide) port sampleCorrect addBound sampleTime sampleWords
      addNames sampleNames tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def executeProgram {A : Type} (input : Representation 16 A) (code : Interactive.Code 16) (budget : Nat)
    (request : A) (replies : List (Word 16)) := do
  let initial := input.initial request
  let before := { initial with
    regs := fun r => if r = 200 then 99 else initial.regs r
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 500000 (code.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200,
    result.state.caps 200, result.state.regs 200, result.state.tapePos,
    (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ budget))

private def execute := executeProgram (CaliperBackend.SchnorrAGM.Read.input layout).representation program
  (CaliperBackend.SchnorrAGM.Read.timeBudget layout 6 4)
private def executeEntry := executeProgram (CaliperBackend.SchnorrAGM.Read.input layout).representation entryProgram
  (CaliperBackend.SchnorrAGM.EntryRead.timeBudget layout 6 4)
private def extractionInput (request : (CaliperBackend.SchnorrAGM.Read.input layout).Value) (z : Word 16) :
    (CaliperBackend.SchnorrAGM.ExtractionRead.input layout).Value := ⟨(request.val, z), request.property, trivial⟩
private def executeExtraction (request : (CaliperBackend.SchnorrAGM.Read.input layout).Value) (z : Word 16) :=
  executeProgram (CaliperBackend.SchnorrAGM.ExtractionRead.input layout).representation extractionProgram
    (CaliperBackend.SchnorrAGM.ExtractionRead.timeBudget layout 6 6 6 4) (extractionInput request z)

private theorem extractionMemory (tape : RandomTape 16) (value : (CaliperBackend.SchnorrAGM.ExtractionRead.input layout).Value) (before : State 16)
    (holds : (CaliperBackend.SchnorrAGM.ExtractionRead.input layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (extractionProgram.execute port .unit tape before)) :
    finished.time ≤ CaliperBackend.SchnorrAGM.ExtractionRead.timeBudget layout 6 6 6 4 ∧
      ∃ answer ∈ support (CaliperBackend.SchnorrAGM.ExtractionRead.source layout trivial add sub divide addNames.buffers subNames.buffers (by decide) sampleSource value),
        (CaliperBackend.SchnorrAGM.Read.output layout).representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape (extractionProgram.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            ((extractionProgram.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (extractionProgram.lower port).memBound) ≤
              5 * CaliperBackend.SchnorrAGM.ExtractionRead.codeBudget layout 27 27 27 20 + 24 + registers + 3 * buffers + before.liveMem buffers +
                CaliperBackend.SchnorrAGM.ExtractionRead.timeBudget layout 6 6 6 4 := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    CaliperBackend.SchnorrAGM.ExtractionRead.resources layout trivial add sub divide addNames.buffers subNames.buffers divNames.buffers (by decide)
      port sampleCorrect addBound subBound divBound sampleTime sampleWords addNames subNames.accounted divNames.accounted sampleNames
      tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def paddedNone : (CaliperBackend.SchnorrAGM.Read.input layout).Value :=
  ⟨((3, 4), (5, 7), [((3, 4), (7, false, 21, 22)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, true, 13, 14))],
    [(1, 0), (0, 1), (11, 13)], [9], true, false), by rw [valid_iff]; decide⟩
private def zeroHit : (CaliperBackend.SchnorrAGM.Read.input layout).Value :=
  ⟨((3, 4), (5, 7), [((3, 4), (0, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, true, 13, 14))],
    [(1, 0), (0, 1), (11, 13)], [9], true, false), by rw [valid_iff]; decide⟩

open Lean in
run_cmd do
  let check := fun request replies (entry : Array (Word 16)) (z answer : Word 16) expected =>
    execute request replies == some expected &&
      executeEntry request replies == some (entry ++ expected.1.extract 1 expected.1.size, expected.2) &&
      executeExtraction request z replies == some (#[answer] ++ expected.1.extract 1 expected.1.size, expected.2)
  unless check duplicate [88] #[2, 1, 9, 10] 33 2
      (#[2, 3, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
        3, 1, 0, 0, 1, 11, 13, 1, 9, 1, 0], [], [88], #[77], 4, 99, 7, true, true) do
    throwError "full read hit sampled, changed metadata, or failed to retain the first duplicate entry"
  unless check (miss false) [9, 88] #[9, 1, 5, 7] 37 2
      (#[9, 2, 3, 4, 9, 1, 5, 7, 5, 6, 1, 1, 13, 14] ++ Array.replicate 6 0 ++
        #[3, 1, 0, 0, 1, 11, 13, 1, 9, 1, 0], [.invoke, .input 9], [88], #[77], 4, 99, 7, true, true) do
    throwError "full read miss lost its cache entry, saved metadata, external frame, or resource bound"
  unless check (miss false) [65529] #[65529, 1, 5, 7] 37 0
      (#[65529, 2, 3, 4, 65529, 1, 5, 7, 5, 6, 1, 1, 13, 14] ++ Array.replicate 6 0 ++
        #[3, 1, 0, 0, 1, 11, 13, 1, 9, 1, 1], [.invoke, .input 65529], [], #[77], 4, 99, 7, true, true) do
    throwError "full read restored the old bad flag over the newly detected exceptional challenge"
  unless check (miss true) [9] #[9, 1, 5, 7] 37 2
      (#[9, 2, 3, 4, 9, 1, 5, 7, 5, 6, 1, 1, 13, 14] ++ Array.replicate 6 0 ++
        #[3, 1, 0, 0, 1, 11, 13, 1, 9, 1, 1], [.invoke, .input 9], [], #[77], 4, 99, 7, true, true) do
    throwError "full read cleared an existing bad flag"
  unless check lastSlot [9] #[9, 1, 5, 7] 37 2
      (#[9, 3, 3, 4, 9, 1, 5, 7, 5, 6, 1, 1, 13, 14, 7, 8, 2, 0, 0, 0,
        3, 1, 0, 0, 1, 11, 13, 1, 9, 0, 0], [.invoke, .input 9], [], #[77], 4, 99, 7, true, true) do
    throwError "final reserved cache slot was not filled or an existing unexplained entry changed"
  unless check changed [4] #[4, 1, 11, 13] 45 2
      (#[4, 1, 8, 12, 4, 1, 11, 13] ++ Array.replicate 12 0 ++
        #[1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0], [.invoke, .input 4], [], #[77], 4, 99, 7, true, true) do
    throwError "read packing captured fixed keys, coefficients or metadata instead of runtime values"
  unless check paddedNone [88] #[7, 0, 21, 22] 100 0
      (#[7, 3, 3, 4, 7, 0, 21, 22, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
        3, 1, 0, 0, 1, 11, 13, 1, 9, 1, 0], [], [88], #[77], 4, 99, 7, true, true) do
    throwError "terminal read skipped the first unexplained entry, changed its padding or returned a nonzero solution"
  unless check zeroHit [88] #[0, 1, 9, 10] 29 2
      (#[0, 3, 3, 4, 0, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
        3, 1, 0, 0, 1, 11, 13, 1, 9, 1, 0], [], [88], #[77], 4, 99, 7, true, true) do
    throwError "terminal read confused a cached zero challenge with a miss or used the new explanation"
  unless execute (miss false) [] == none && executeEntry (miss false) [] == none && executeExtraction (miss false) 37 [] == none do
    throwError "full read miss succeeded without its scalar reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``StatefulCacheRead.buffers, ``CaliperBackend.SchnorrAGM.Read.pack, ``CaliperBackend.SchnorrAGM.Read.finish,
      ``CaliperBackend.SchnorrAGM.Read.refines, ``CaliperBackend.SchnorrAGM.Read.source_original,
      ``CaliperBackend.SchnorrAGM.Read.reserved_input, ``CaliperBackend.SchnorrAGM.Read.time_bound,
      ``CaliperBackend.SchnorrAGM.Read.code_bound, ``CaliperBackend.SchnorrAGM.Read.names,
      ``CaliperBackend.SchnorrAGM.Read.buffers, ``CaliperBackend.SchnorrAGM.Read.descriptionFits,
      ``CaliperBackend.SchnorrAGM.Read.resources, ``refined, ``timed, ``stored, ``accepted, ``buffers, ``memory, ``entryRefined, ``entryTimed, ``entryStored, ``entryAccepted, ``entryBuffers,
      ``CaliperBackend.SchnorrAGM.EntryRead.finish, ``CaliperBackend.SchnorrAGM.EntryRead.refines,
      ``CaliperBackend.SchnorrAGM.EntryRead.source_original, ``CaliperBackend.SchnorrAGM.EntryRead.time_bound,
      ``CaliperBackend.SchnorrAGM.EntryRead.code_bound, ``CaliperBackend.SchnorrAGM.EntryRead.names,
      ``CaliperBackend.SchnorrAGM.EntryRead.buffers, ``CaliperBackend.SchnorrAGM.EntryRead.descriptionFits, ``CaliperBackend.SchnorrAGM.EntryRead.resources,
      ``CaliperBackend.SchnorrAGM.ExtractionArithmetic.implementation, ``CaliperBackend.SchnorrAGM.ExtractionArithmetic.bounded,
      ``CaliperBackend.SchnorrAGM.ExtractionArithmetic.names, ``CaliperBackend.SchnorrAGM.ExtractionArithmetic.value_encode,
      ``CaliperBackend.SchnorrAGM.ExtractionRead.prepare, ``CaliperBackend.SchnorrAGM.ExtractionRead.refines,
      ``CaliperBackend.SchnorrAGM.ExtractionRead.time_bound, ``CaliperBackend.SchnorrAGM.ExtractionRead.code_bound,
      ``CaliperBackend.SchnorrAGM.ExtractionRead.names, ``CaliperBackend.SchnorrAGM.ExtractionRead.descriptionFits,
      ``CaliperBackend.SchnorrAGM.ExtractionRead.source_original, ``CaliperBackend.SchnorrAGM.ExtractionRead.resources,
      ``extractionRefined, ``extractionTimed, ``extractionStored, ``extractionAccepted, ``extractionMemory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMRead
