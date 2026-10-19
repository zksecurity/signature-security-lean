import Signatures.Runtime.Caliper.SchnorrAGMHashMemory
import Lean

open Caliper OracleComp OracleSpec Signatures.Runtime Signatures.Runtime.CaliperBackend BoundedSource
namespace SignaturesTest.CaliperSchnorrAGMHash

-- Modular-word arithmetic tests the executed wiring. The generic source
-- theorem separately covers field arithmetic and the uniform challenge law.
private def scheme : CaliperBackend.SchnorrAGM.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scalar := Layout.all (wordRepresentation 16 (by decide))
  point := Layout.all (wordRepresentation 16 (by decide))
  message := Layout.counter 16 256 (by decide) (by decide)
  wordFits := by decide
  countFits := by decide
  storageFits := by decide
private def layout : CaliperBackend.SchnorrAGM.Hash.Layouts 16 Nat (Word 16) (Word 16) 1 1 where
  scheme := scheme
  coefficients := 5
  counterFits := by decide
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

private def program := CaliperBackend.SchnorrAGM.Hash.code layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler
private theorem refined : Interactive.Refines port .unit layout.input.representation
    (CaliperBackend.SchnorrAGM.Read.output scheme).representation
    (CaliperBackend.SchnorrAGM.Hash.source layout trivial mul add mulNames.buffers addNames.buffers (by decide) sampleSource) program :=
  CaliperBackend.SchnorrAGM.Hash.refines layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampleCorrect
private theorem timed : Interactive.TimeBound port .unit layout.input.representation program
    (CaliperBackend.SchnorrAGM.Hash.timeBudget layout 6 6 4) :=
  CaliperBackend.SchnorrAGM.Hash.time_bound layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampleCorrect
    mulBound addBound sampleTime
private theorem stored : (program.lower port).descriptionWords ≤ CaliperBackend.SchnorrAGM.Hash.codeBudget layout 27 27 20 :=
  CaliperBackend.SchnorrAGM.Hash.code_bound layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler
    mulBound addBound sampleWords
private theorem accepted : (program.lower port).DescriptionFits :=
  CaliperBackend.SchnorrAGM.Hash.descriptionFits layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler
    sampleFits addNames sampleNames (by decide)
private theorem buffers : (program.lower port).memBound ≤ 11 :=
  CaliperBackend.SchnorrAGM.Hash.buffers layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampler addNames sampleNames

private theorem valid_iff (key : Nat × Word 16) (coefficients : List (Word 16))
    (entries : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)))
    (basis : List (Word 16 × Word 16)) (signed : List Nat) (malformed bad : Bool) :
    layout.input.valid (key, coefficients, entries, basis, signed, malformed, bad) ↔
      (key.1 < 256 ∧ coefficients.length ≤ 5 ∧ (entries.length ≤ 3 ∧ ∀ entry ∈ entries, entry.1.1 < 256) ∧
        basis.length ≤ 3 ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256)) ∧
          ((cacheMap entries key).isNone = true → entries.length ≤ 2) := by
  change (((key.1 < 256 ∧ True) ∧ (coefficients.length ≤ 5 ∧ ∀ coefficient ∈ coefficients, True) ∧
    (entries.length ≤ 3 ∧ ∀ entry ∈ entries, (entry.1.1 < 256 ∧ True) ∧ (True ∧ True ∧ True ∧ True)) ∧
    (basis.length ≤ 3 ∧ ∀ pair ∈ basis, True ∧ True) ∧ (signed.length ≤ 1 ∧ ∀ message ∈ signed, message < 256) ∧ True ∧ True) ∧ _) ↔ _
  simp only [and_true, implies_true]
  rfl

private def full : List ((Nat × Word 16) × SchnorrAGM.Native.EncodedEntry (Word 16)) :=
  [((3, 4), (2, true, 9, 10)), ((3, 4), (8, true, 11, 12)), ((5, 6), (1, true, 13, 14))]
private def duplicate : layout.input.Value :=
  ⟨((3, 4), [2, 3, 4], full, [(1, 0), (0, 1), (5, 7)], [9], true, false), by rw [valid_iff]; decide⟩
private def miss (basis : List (Word 16 × Word 16)) (coefficients : List (Word 16))
    (fits : basis.length ≤ 3 ∧ coefficients.length ≤ 5) (bad : Bool) : layout.input.Value :=
  ⟨((3, 4), coefficients, [((5, 6), (1, true, 13, 14))], basis, [9], true, bad), by
    rw [valid_iff]
    exact ⟨⟨by decide, fits.2, by decide, fits.1, by decide⟩, fun _ => by decide⟩⟩
private def lastSlot : layout.input.Value :=
  ⟨((3, 4), [2, 3, 4], [((5, 6), (1, true, 13, 14)), ((7, 8), (2, false, 0, 0))],
    [(1, 0), (0, 1), (5, 7)], [9], false, false), by rw [valid_iff]; decide⟩

example : ¬ layout.input.valid ((7, 8), [2], full, [(1, 0), (0, 1)], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ((256, 8), [2], [], [(1, 0), (0, 1)], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ((7, 8), List.replicate 6 0, [], [], [], false, false) := by rw [valid_iff]; decide
example : ¬ layout.input.valid ((7, 8), [], [], List.replicate 4 (0, 0), [], false, false) := by rw [valid_iff]; decide

private theorem memory (tape : RandomTape 16) (value : layout.input.Value) (before : State 16)
    (holds : layout.input.representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result 16) (reached : some finished ∈ support (program.execute port .unit tape before)) :
    finished.time ≤ CaliperBackend.SchnorrAGM.Hash.timeBudget layout 6 6 4 ∧
      ∃ answer ∈ support (CaliperBackend.SchnorrAGM.Hash.source layout trivial mul add mulNames.buffers addNames.buffers (by decide) sampleSource value),
        (CaliperBackend.SchnorrAGM.Read.output scheme).representation.Holds answer finished.state ∧
        ∃ execution : WordIO.Exec .unit tape (program.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
          ∀ between, execution.Visits between →
            ((program.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (program.lower port).memBound) ≤
              5 * CaliperBackend.SchnorrAGM.Hash.codeBudget layout 27 27 20 + 24 + registers + 3 * buffers + before.liveMem buffers +
                CaliperBackend.SchnorrAGM.Hash.timeBudget layout 6 6 4 := by
  obtain ⟨elapsed, answer, supported, result, execution, bounds⟩ :=
    CaliperBackend.SchnorrAGM.Hash.resources layout trivial mul add mulNames.buffers addNames.buffers (by decide) port sampleCorrect
      mulBound addBound sampleTime sampleWords mulNames addNames sampleNames tape value before holds registers buffers initialRegisters initialBuffers finished reached
  exact ⟨elapsed, answer, supported, result, execution, fun between visited => (bounds between visited).2.2.2⟩

private def execute (request : layout.input.Value) (replies : List (Word 16)) := do
  let initial := layout.input.representation.initial request
  let before := { initial with
    regs := fun r => if r = 200 then 99 else initial.regs r
    bufs := fun b => if b = 200 then #[77] else initial.bufs b
    caps := fun b => if b = 200 then 4 else initial.caps b
    tapePos := 7 }
  let result ← WordIO.run .unit RandomTape.zero 1000000 (program.lower port) before replies
  pure (result.state.bufs 0, result.trace, result.remaining, result.state.bufs 200,
    result.state.caps 200, result.state.regs 200, result.state.tapePos,
    (List.range 30).all (fun i => result.state.caps (i + 1) == 0),
    decide (result.time ≤ CaliperBackend.SchnorrAGM.Hash.timeBudget layout 6 6 4))

open Lean in
run_cmd do
  let check := fun input replies bytes trace remaining =>
    execute input replies == some (bytes, trace, remaining, #[77], 4, 99, 7, true, true)
  unless check duplicate [88]
      #[2, 3, 3, 4, 2, 1, 9, 10, 3, 4, 8, 1, 11, 12, 5, 6, 1, 1, 13, 14,
        3, 1, 0, 0, 1, 5, 7, 1, 9, 1, 0] [] [88] do
    throwError "hash cache hit sampled, replaced the first explanation, or changed retained state"
  let basis := [(1, 0), (0, 1), (5, 7)]
  let expected := fun challenge a b basisBytes bad =>
    #[challenge, 2, 3, 4, challenge, 1, a, b, 5, 6, 1, 1, 13, 14] ++ Array.replicate 6 0 ++ basisBytes ++ #[1, 9, 1, bad]
  unless check (miss basis [2, 3, 4] (by decide) false) [9, 88]
      (expected 9 22 31 #[3, 1, 0, 0, 1, 5, 7] 0) [.invoke, .input 9] [88] do
    throwError "hash miss lost the flattened explanation, original metadata, external frame or resource bound"
  unless check (miss basis [2, 3, 4] (by decide) false) [65505]
      (expected 65505 22 31 #[3, 1, 0, 0, 1, 5, 7] 1) [.invoke, .input 65505] [] do
    throwError "exceptional challenge did not use the computed secret coefficient or failed to update bad"
  unless check (miss basis [2, 3, 4] (by decide) true) [9]
      (expected 9 22 31 #[3, 1, 0, 0, 1, 5, 7] 1) [.invoke, .input 9] [] do
    throwError "hash request cleared an existing bad flag"
  unless check (miss basis [2] (by decide) false) [9]
      (expected 9 2 0 #[3, 1, 0, 0, 1, 5, 7] 0) [.invoke, .input 9] [] do
    throwError "hash request failed to default missing coefficients to zero"
  unless check (miss basis [2, 3, 4, 99, 100] (by decide) false) [9]
      (expected 9 22 31 #[3, 1, 0, 0, 1, 5, 7] 0) [.invoke, .input 9] [] do
    throwError "surplus coefficients changed the hash explanation"
  unless check (miss [(5, 7), (0, 1), (1, 0)] [2, 3, 4] (by decide) false) [9]
      (expected 9 14 17 #[3, 5, 7, 0, 1, 1, 0] 0) [.invoke, .input 9] [] do
    throwError "hash request ignored current basis order"
  unless check (miss [] [2, 3] (by decide) false) [9]
      (expected 9 0 0 (Array.replicate 7 0) 0) [.invoke, .input 9] [] do
    throwError "empty basis failed to produce zero or restore its original encoding"
  unless check lastSlot [9]
      #[9, 3, 3, 4, 9, 1, 22, 31, 5, 6, 1, 1, 13, 14, 7, 8, 2, 0, 0, 0,
        3, 1, 0, 0, 1, 5, 7, 1, 9, 0, 0] [.invoke, .input 9] [] do
    throwError "hash request failed to fill the final reserved slot"
  unless execute (miss basis [2, 3, 4] (by decide) false) [] == none do
    throwError "hash miss succeeded without a challenge reply"
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``CaliperBackend.SchnorrAGM.Hash.pack, ``CaliperBackend.SchnorrAGM.Hash.finish,
      ``CaliperBackend.SchnorrAGM.Hash.prepare, ``CaliperBackend.SchnorrAGM.Hash.refines,
      ``CaliperBackend.SchnorrAGM.Hash.source_original, ``CaliperBackend.SchnorrAGM.Hash.reserved_input,
      ``CaliperBackend.SchnorrAGM.Hash.time_bound, ``CaliperBackend.SchnorrAGM.Hash.code_bound,
      ``CaliperBackend.SchnorrAGM.Hash.names, ``CaliperBackend.SchnorrAGM.Hash.buffers,
      ``CaliperBackend.SchnorrAGM.Hash.descriptionFits, ``CaliperBackend.SchnorrAGM.Hash.resources,
      ``refined, ``timed, ``stored, ``accepted, ``buffers, ``memory] do
    for dependency in (← collectAxioms name) do
      unless dependency ∈ allowed do throwError "unexpected axiom {dependency} in {name}"

end SignaturesTest.CaliperSchnorrAGMHash
