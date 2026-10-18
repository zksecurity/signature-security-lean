import Signatures.Runtime.Caliper.SourceMemory
import Signatures.Runtime.Caliper.InteractiveDescription
import Signatures.Runtime.Caliper.Words
import Lean

open Caliper OracleComp OracleSpec PFunctor Signatures.Runtime Signatures.Runtime.CaliperBackend

namespace SignaturesTest.CaliperInteractive

-- This class labels the old source syntax only. Its fake costs are never used
-- for the target: every compilation leaf below supplies actual Caliper code.
private def syntaxClass : StepClass.{0, 0} where
  Str _ := PUnit
  Hom _ _ _ := True
  id_mem _ := trivial
  comp_mem _ _ := trivial

private instance : syntaxClass.HasProd where
  prod _ _ := PUnit.unit
  fst_mem _ _ := trivial
  snd_mem _ _ := trivial
  pair_mem _ _ := trivial

private instance : syntaxClass.HasSum where
  sum _ _ := PUnit.unit
  inl_mem _ _ := trivial
  inr_mem _ _ := trivial
  elim_mem _ _ := trivial

private def syntaxQ : QuantitativeStepClass.{0, 0, 0} syntaxClass where
  Realizer _ _ _ := Unit
  size _ _ := 0
  cost _ _ := 0
  admissible _ := trivial

private def sampleSpec : OracleSpec Nat := fun _ => Fin 4
private def sourceIface : BackendProgram.Interface (C := syntaxClass) sampleSpec := ⟨⟨⟩, ⟨⟩⟩
private def counter := BoundedSource.Layout.counter 8 16 (by decide) (by decide)
private def answerRep := Representation.fin 8 4 (by decide) (by decide)
private def targetIface : SourceCompilation.Interface 8 sampleSpec where
  request := counter
  reply := (counter.representation.prod answerRep (by decide)).transport
    { toFun := fun value => (value.1, value.2)
      invFun := fun value => ⟨value.1, value.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private def answerValue (value : Σ i, sampleSpec.Range i) : Nat := value.2.val
private def projection : BoundedSource.Implementation .unit targetIface.response counter answerValue where
  preserves value _ := lt_of_lt_of_le value.2.isLt (by decide)
  program := selectSliceRealizer .unit (by decide) targetIface.response.representation counter.representation
    (fun value => ⟨answerValue value.val, lt_of_lt_of_le value.val.2.isLt (by decide)⟩) 1
    (by decide) (by decide) (fun _ => rfl)

private def tagged := counter.sum counter (by decide) (by decide)
private def continueImpl : BoundedSource.Implementation .unit counter tagged (fun n => Sum.inr n) where
  preserves _ valid := valid
  program := (inrRealizer .unit (by decide) counter.representation counter.representation (by decide) (by decide)).viewOutput
    tagged.representation (fun value => ⟨Sum.inr value.val, value.property⟩) (fun _ => rfl)

private def requestAnswer : BackendProgram.Code syntaxQ sampleSpec sourceIface
    (A := Nat) (B := Nat)
    (PUnit.unit : syntaxClass.Str Nat) (PUnit.unit : syntaxClass.Str Nat) :=
  .seq .query (.atomic (f := answerValue) ())
private def requestAnswerCode : SourceCompilation.Compilation targetIface WordIO.Costs.unit (by decide)
    requestAnswer counter counter := .seq .query
      (.atomic (Q := syntaxQ) (sourceIface := sourceIface)
        (a := PUnit.unit) (b := PUnit.unit) (f := answerValue) () projection)

private def step : BackendProgram.Code syntaxQ sampleSpec sourceIface
    (A := Nat) (B := Nat ⊕ Nat)
    (PUnit.unit : syntaxClass.Str Nat)
    (StepClass.HasSum.sum (A := Nat) (B := Nat) (PUnit.unit : syntaxClass.Str Nat) PUnit.unit) :=
  .seq requestAnswer (.atomic (f := fun n => Sum.inr n) ())
private def stepCode : SourceCompilation.Compilation targetIface WordIO.Costs.unit (by decide) step counter tagged :=
  .seq requestAnswerCode (.atomic (Q := syntaxQ) (sourceIface := sourceIface)
    (a := PUnit.unit) (b := PUnit.unit) (f := fun n : Nat => (Sum.inr n : Nat ⊕ Nat)) () continueImpl)
private def stop : BackendProgram.Code syntaxQ sampleSpec sourceIface
    (A := Nat) (B := Nat)
    (PUnit.unit : syntaxClass.Str Nat) (PUnit.unit : syntaxClass.Str Nat) := .atomic (f := id) ()
private def stopCode : SourceCompilation.Compilation targetIface WordIO.Costs.unit (by decide) stop counter counter :=
  .atomic (Q := syntaxQ) (sourceIface := sourceIface)
    (a := PUnit.unit) (b := PUnit.unit) (f := id (α := Nat)) ()
    (BoundedSource.Implementation.identity counter (by decide))
private def loopCode (fuel : Nat) := SourceCompilation.Compilation.loop (by decide) stepCode stopCode fuel

private def requestBounds : requestAnswerCode.LocalBounds := ((), ⟨8, fun _ => le_rfl⟩)
private def stepBounds : stepCode.LocalBounds := (requestBounds, ⟨15, fun _ => le_rfl⟩)
private def loopBounds (fuel : Nat) : (loopCode fuel).LocalBounds := (stepBounds, ⟨0, fun _ => le_rfl⟩)

example : (loopCode 2).timeBudget (loopBounds 2) = 86 := by decide

-- A uniform result, over every represented initial state, tape and adaptive
-- oracle reply sequence, rather than just the particular execution below.
example (tape : RandomTape 8) (value : counter.Value) (before : State 8)
    (holds : counter.representation.Holds value before) (finished : WordIO.Result 8)
    (reached : some finished ∈ support ((loopCode 2).compile.execute targetIface.port .unit tape before)) :
    finished.time ≤ 86 ∧ finished.peak ≤ 86 :=
  (loopCode 2).resources (loopBounds 2) (by decide) tape value before holds finished reached

-- The second oracle request depends on the first reply. Both exchanges and all
-- loop dispatch/projection instructions execute; there is no free caller resume.
example : (WordIO.run .unit RandomTape.zero 200 ((loopCode 2).compile.lower targetIface.port)
    (counter.representation.initial ⟨7, by change 7 < 16; decide⟩) [7, 3, 3, 2]).map
    (fun result => (result.state.bufs 0, result.time, result.trace)) =
    some (#[2], 86, [.output 7, .invoke, .input 7, .input 3,
      .output 3, .invoke, .input 3, .input 2]) := by decide

-- The theorem concerns the original source program, including its Nat query
-- positions. No universal finite encoding of Nat is assumed.
example (tape : RandomTape 8) (value : counter.Value) :
    (fun result => Subtype.val <$> Interactive.observe counter.representation result) <$>
      (loopCode 2).compile.execute targetIface.port .unit tape (counter.representation.initial value) =
    some <$> (BackendProgram.Code.loop step stop 2).denote value.val :=
  (loopCode 2).observe (by decide) tape value _ (counter.representation.initial_holds value)

private def saved := BoundedSource.Layout.all (wordRepresentation 8 (by decide))
private def retainedSource := BackendProgram.Code.first
  (S := Word 8)
  (PUnit.unit : syntaxClass.Str (Word 8)) requestAnswer
private def retainedCode := SourceCompilation.Compilation.first
  (S := Word 8)
  (PUnit.unit : syntaxClass.Str (Word 8)) saved requestAnswerCode (by decide) (by decide)
private def retainedInput := (counter.prod saved (by decide)).representation.initial
  ⟨(7, 99), (by change 7 < 16; decide), trivial⟩

example : retainedCode.timeBudget requestBounds = 46 := by decide

example (tape : RandomTape 8) (value : (counter.prod saved (by decide)).Value) (before : State 8)
    (holds : (counter.prod saved (by decide)).representation.Holds value before) (finished : WordIO.Result 8)
    (reached : some finished ∈ support (retainedCode.compile.execute targetIface.port .unit tape before)) :
    finished.time ≤ 46 ∧ finished.peak ≤ 46 :=
  retainedCode.resources requestBounds (by decide) tape value before holds finished reached

example : Interactive.savedBuffer targetIface.port requestAnswerCode.compile = 2 := by decide
example : (WordIO.run .unit RandomTape.zero 200 (retainedCode.compile.lower targetIface.port) retainedInput [7, 3]).map
    (fun result => ((result.state.bufs 0, result.state.caps 1, result.state.caps 2),
      (result.time, result.net, result.peak))) = some ((#[3, 99], 0, 0), (46, 0, 3)) := by decide

example : ((loopCode 2).compile.lower targetIface.port).descriptionWords = 484 := by
  change ((Interactive.loop stepCode.compile stopCode.compile 1 1 2).lower targetIface.port).descriptionWords = 484
  rw [Interactive.loop_descriptionWords]
  have body : (stepCode.compile.lower targetIface.port).descriptionWords = 146 := by
    change (WordIO.Code.seq (requestAnswerCode.compile.lower targetIface.port)
      (.compute continueImpl.program.code)).descriptionWords = 146
    rw [WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
    have request : (requestAnswerCode.compile.lower targetIface.port).descriptionWords = 83 := by decide
    rw [request]
    decide
  have stop : (stopCode.compile.lower targetIface.port).descriptionWords = 2 := by decide
  rw [body, stop]
private theorem retained_words : (retainedCode.compile.lower targetIface.port).descriptionWords = 215 := by
  change ((Interactive.retain requestAnswerCode.compile 2 1 1 1).lower targetIface.port).descriptionWords = 215
  simp only [Interactive.retain, Interactive.Code.lower, WordIO.Code.descriptionWords_seq,
    WordIO.Code.descriptionWords_compute]
  have body : (requestAnswerCode.compile.lower targetIface.port).descriptionWords = 83 := by decide
  rw [body]
  decide

private theorem retained_registers : (retainedCode.compile.lower targetIface.port).registerSlots = 3 := by decide
private theorem retained_buffers : (retainedCode.compile.lower targetIface.port).memBound = 3 := by decide
private theorem retained_static : (retainedCode.compile.lower targetIface.port).staticWords 0 1 = 227 := by
  simp only [WordIO.Code.staticWords, retained_words, retained_registers, retained_buffers]
  decide
private theorem retained_memoryBudget : retainedCode.memoryBudget requestBounds retainedInput 0 1 = 275 := by
  simp only [SourceCompilation.Compilation.memoryBudget, retained_static, retained_buffers]
  change 227 + 2 + 46 = 275
  decide

-- The bound includes the entire 215-word program, 3 register slots, 9 descriptor
-- words, the 2-word initial input, and conservative dynamic growth. It covers
-- every intermediate state, including those inside the local copy routines.
example (tape : RandomTape 8) (finished : WordIO.Result 8)
    (reached : some finished ∈ support (retainedCode.compile.execute targetIface.port .unit tape retainedInput)) :
    ∃ execution : WordIO.Exec .unit tape (retainedCode.compile.lower targetIface.port) retainedInput finished.state
        finished.trace finished.time finished.net finished.peak,
      ∀ between, execution.Visits between →
        RegisterBound between 3 ∧ between.SupportBound 3 ∧ between.WellFormed ∧
        227 + (between.liveMem 3 : Int) ≤ 275 := by
  have represented := (counter.prod saved (by decide)).representation.initial_holds
    (⟨(7, 99), (by change 7 < 16; decide), trivial⟩ : (counter.prod saved (by decide)).Value)
  have initialRegisters : RegisterBound retainedInput 0 := fun _ _ => rfl
  have initialBuffers : retainedInput.SupportBound 1 := by
    intro buffer outside
    simp [retainedInput, Representation.initial, show buffer ≠ 0 by omega]
  simpa only [retained_memoryBudget, retained_static, retained_registers, retained_buffers,
    Nat.zero_max, Nat.cast_ofNat, show max 1 3 = 3 from rfl] using
    retainedCode.memoryBound requestBounds (by decide) tape _ retainedInput represented
      0 1 initialRegisters initialBuffers finished reached


open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``Synchronizes.bind, ``Synchronizes.map_eq, ``Synchronizes.right_support,
      ``Interactive.Refines.compute, ``Interactive.Refines.query, ``Interactive.Refines.seq,
      ``Interactive.Refines.dispatch, ``Interactive.Refines.loop, ``Interactive.Refines.retain,
      ``SourceCompilation.Compilation.correct, ``SourceCompilation.Compilation.erase,
      ``SourceCompilation.Compilation.observe, ``Interactive.loop_descriptionWords,
      ``Interactive.retain_descriptionWords_le, ``WordIO.Exec.net_le_time, ``WordIO.Exec.peak_le_time,
      ``Interactive.TimeBound.seq, ``Interactive.TimeBound.dispatch, ``Interactive.TimeBound.retain,
      ``Interactive.TimeBound.loop, ``Interactive.TimeBound.bufferPeak,
      ``Interactive.retain_time_unit_le, ``SourceCompilation.Compilation.timeBound,
      ``SourceCompilation.Compilation.resources, ``WordIO.Exec.liveMem_eq,
      ``WordIO.Exec.Visits.liveMem_le_peak, ``WordIO.Exec.Visits.total_memory_bound,
      ``SourceCompilation.Compilation.memoryBound] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperInteractive
