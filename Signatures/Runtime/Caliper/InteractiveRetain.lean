import Signatures.Runtime.Caliper.InteractiveControl
import Signatures.Runtime.Caliper.Retain

/-! Saved caller state across interactive Caliper code. The saved buffer lies
beyond every buffer touched by the lowered callee, including its oracle adapter.
Saving, selecting the argument, rebuilding the pair and release are all executed
Caliper instructions. No host pair or uncharged snapshot stores the payload.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper Assembly

variable {w : Nat}

def WordIO.Code.memBound : WordIO.Code w → Nat
  | .compute code => code.memBound
  | .read _ | .write _ | .invoke => 0
  | .seq first second => max first.memBound second.memBound
  | .branch _ yes no => max yes.memBound no.memBound

theorem WordIO.Code.touches_lt_memBound {code : WordIO.Code w} {buffer : BufId}
    (touched : code.Touches buffer) : buffer < code.memBound := by
  induction code with
  | compute code => exact Stmt.touches_lt_memBound touched
  | read | write | invoke => cases touched
  | seq first second ih₁ ih₂ | branch condition first second ih₁ ih₂ =>
    exact touched.elim (fun h => lt_of_lt_of_le (ih₁ h) (le_max_left _ _))
      (fun h => lt_of_lt_of_le (ih₂ h) (le_max_right _ _))

namespace Retain

def prepare (buffer inputWords savedWords : Nat) : Stmt w :=
  save buffer inputWords savedWords ;; selectSlice 0 inputWords

def finish (buffer outputWords savedWords : Nat) : Stmt w :=
  Assembly.code (restoreOperands buffer outputWords savedWords) ;; .memFree buffer

theorem prepare_exec {A S : Type} (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (tape : RandomTape w) (input : Representation w A) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (fits : input.encoding.words + saved.encoding.words < 2 ^ w)
    (buffer : Nat) (reserved : 2 ≤ buffer) (value : A × S) (before : State w)
    (represented : (input.prod saved fits).Holds value before) :
    ∃ after time net peak, Caliper.Exec cost tape (prepare buffer input.encoding.words saved.encoding.words)
      before after time net peak ∧ input.Holds value.1 after ∧
      (after.bufs buffer).toList = saved.encoding.encode value.2 := by
  have h0 : buffer ≠ 0 := by omega
  have h1 : buffer ≠ 1 := by omega
  have size := represented_size (input.prod saved fits) represented
  obtain ⟨stored, ts, ds, ps, storing, savedContents, original, zero, capacities⟩ :=
    save_exec cost tape buffer input.encoding.words saved.encoding.words before h0
      (by simpa [Representation.prod, Encoding.prod, Encoding.checked] using size.ge)
      (by rw [size]; exact fits) represented.2.2.2
  have savedValue : (stored.bufs buffer).toList = saved.encoding.encode value.2 := by
    rw [savedContents, represented.2.1]
    change ((input.encoding.encode value.1 ++ saved.encoding.encode value.2).drop input.encoding.words).take saved.encoding.words = _
    rw [← input.encoding.encode_length value.1, ← saved.encoding.encode_length value.2]
    simp
  have storedInput : (input.prod saved fits).Holds value stored :=
    ⟨zero.trans represented.1, by rw [original]; exact represented.2.1,
      storing.wellFormed_preserved represented.2.2.1, capacities⟩
  obtain ⟨projected, dp, pp, projecting, result, _, _⟩ :=
    (firstRealizer cost allocation input saved hw fits).correct tape value stored storedInput
  refine ⟨projected, _, _, _, .seq storing projecting, result, ?_⟩
  rw [projecting.frame_buf (select_untouched _ _ _ h0 h1), savedValue]

theorem finish_exec {B S : Type} (cost : CostModel) (tape : RandomTape w)
    (output : Representation w B) (saved : Representation w S)
    (fits : output.encoding.words + saved.encoding.words < 2 ^ w)
    (buffer : Nat) (reserved : 2 ≤ buffer) (value : B × S) (before : State w)
    (represented : output.Holds value.1 before)
    (savedValue : (before.bufs buffer).toList = saved.encoding.encode value.2) :
    ∃ after time net peak, Caliper.Exec cost tape (finish buffer output.encoding.words saved.encoding.words)
      before after time net peak ∧ (output.prod saved fits).Holds value after := by
  have h0 : buffer ≠ 0 := by omega
  have h1 : buffer ≠ 1 := by omega
  have savedSize : (before.bufs buffer).size = saved.encoding.words := by
    have := congrArg List.length savedValue
    simpa [saved.encoding.encode_length] using this
  let operands := restoreOperands (w := w) buffer output.encoding.words saved.encoding.words
  have valid : Valid 1 before operands := by
    intro operand member
    rcases List.mem_append.mp member with left | right
    · exact reads_valid 1 0 0 _ before (by decide)
        (by simp [represented_size output represented])
        (by rw [represented_size output represented]; exact output.fits) operand left
    · exact reads_valid 1 _ 0 _ before h1 (by simp [savedSize])
        (by rw [savedSize]; exact saved.fits) operand right
  obtain ⟨rebuilt, tr, dr, pr, rebuilding, contents, zero, capacities⟩ :=
    Assembly.code_exec cost tape operands before valid
      (by simpa [operands, restoreOperands, reads_length] using fits) represented.2.2.2
  have rebuiltValue : (rebuilt.bufs 0).toList = (output.prod saved fits).encoding.encode value := by
    rw [contents]
    have left := reads_values 0 0 output.encoding.words before (by simp [represented_size output represented])
    have right := reads_values buffer 0 saved.encoding.words before (by simp [savedSize])
    change values (reads 0 0 output.encoding.words ++ reads buffer 0 saved.encoding.words) before =
      output.encoding.encode value.1 ++ saved.encoding.encode value.2
    simp only [values, List.map_append] at *
    rw [left, right, List.drop_zero, List.drop_zero, represented.2.1, savedValue,
      ← output.encoding.encode_length value.1, ← saved.encoding.encode_length value.2]
    simp
  let after := rebuilt.allocBuf buffer 0
  have execution := Caliper.Exec.seq rebuilding (Caliper.Exec.memFree (b := buffer))
  refine ⟨after, _, _, _, execution, zero.trans represented.1, ?_,
    execution.wellFormed_preserved represented.2.2.1, ?_⟩
  · simpa [after, Ne.symm h0] using rebuiltValue
  · intro b
    change (if b = buffer then 0 else rebuilt.caps b) < 2 ^ w
    split_ifs <;> first | positivity | exact capacities b

end Retain

namespace Interactive

open OracleComp OracleSpec

variable {I A B S : Type} {spec : OracleSpec I}

def savedBuffer (port : Port w spec) (body : Code w) : Nat := max 2 (body.lower port).memBound

def retain (body : Code w) (buffer inputWords outputWords savedWords : Nat) : Code w :=
  .seq (.compute (Retain.prepare buffer inputWords savedWords))
    (.seq body (.compute (Retain.finish buffer outputWords savedWords)))

theorem Refines.retain {port : Port w spec} {cost : WordIO.Costs}
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {body : Code w}
    (bodyRefines : Refines port cost input output source body)
    (allocation : 1 ≤ cost.machine.allocPerWord) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (inputFits : input.encoding.words + saved.encoding.words < 2 ^ w)
    (outputFits : output.encoding.words + saved.encoding.words < 2 ^ w) :
    Refines port cost (input.prod saved inputFits) (output.prod saved outputFits)
      (fun value => (fun result => (result, value.2)) <$> source value.1)
      (Interactive.retain body (savedBuffer port body) input.encoding.words output.encoding.words saved.encoding.words) := by
  intro tape value before represented
  let buffer := savedBuffer port body
  have reserved : 2 ≤ buffer := le_max_left _ _
  obtain ⟨prepared, tp, dp, pp, preparing, argument, savedValue⟩ :=
    Retain.prepare_exec cost.machine allocation tape input saved hw inputFits buffer reserved value before represented
  apply prepend_exec port cost tape preparing
  have related := bodyRefines tape value.1 prepared argument
  simp only [Code.execute]
  rw [← bind_pure_comp]
  apply related.bind (fun result => pure (result, value.2))
    (fun result => match result with
      | none => pure none
      | some left => (fun right => join left <$> right) <$>
        Code.execute port cost tape (.compute (Retain.finish buffer output.encoding.words saved.encoding.words)) left.state)
  intro answer result realization
  obtain ⟨called, rfl, outputValue, _, execution⟩ := realization
  have untouched : ¬ (body.lower port).Touches buffer := by
    intro touched
    exact Nat.not_lt_of_ge (le_max_right 2 (body.lower port).memBound) (WordIO.Code.touches_lt_memBound touched)
  have savedAfter : (called.state.bufs buffer).toList = saved.encoding.encode value.2 := by
    rw [(execution.frame_buf untouched).1, savedValue]
  obtain ⟨finished, tf, df, pf, finishing, outputPair⟩ :=
    Retain.finish_exec cost.machine tape output saved outputFits buffer reserved (answer, value.2) called.state outputValue savedAfter
  dsimp only
  rw [execute_of_exec port cost tape finishing]
  simp only [map_pure]
  exact .pure ⟨join called ⟨finished, tf, df, pf, [], []⟩, rfl, outputPair, rfl,
    .seq execution (.compute finishing)⟩

end Interactive
end Signatures.Runtime.CaliperBackend
