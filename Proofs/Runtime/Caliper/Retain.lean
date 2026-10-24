import Proofs.Runtime.Caliper.Assembly

/-! Saved-state composition for bounded pairs. The saved payload is copied to
a buffer beyond the callee's mutation footprint. It remains physically resident
during the call. The output pair is rebuilt by actual reads and writes, then the
saved buffer is freed. No host pair or snapshot operation is a machine primitive.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper Assembly

variable {w : Nat}

namespace Retain

def save (buffer start count : Nat) : Stmt w :=
  .memAllocI buffer count ;; copySlice 0 buffer start count

theorem save_straight (buffer start count : Nat) : (save (w := w) buffer start count).Straight := by
  simp [save, Stmt.Straight, copySlice_straight]

theorem save_randomFree (buffer start count : Nat) : (save (w := w) buffer start count).RandomFree := by
  simp [save, Stmt.RandomFree, copySlice_randomFree]

theorem save_descriptionWords (buffer start count : Nat) :
    descriptionWords (save (w := w) buffer start count) = 13 * count + 5 := by
  simp only [save, descriptionWords_seq, copySlice_descriptionWords]
  simp only [descriptionWords, description, List.length_cons, List.length_nil]
  omega

theorem save_descriptionFits (buffer start count : Nat) (hw : 16 < 2 ^ w)
    (hb : buffer < 2 ^ w) (hc : count < 2 ^ w) : DescriptionFits (save (w := w) buffer start count) := by
  apply DescriptionFits.seq (width_pos hw)
  · simp [DescriptionFits, description, hb, hc]; omega
  · exact copySlice_descriptionFits 0 buffer start count hw (by positivity) hb

theorem select_untouched (buffer start count : Nat) (h0 : buffer ≠ 0) (h1 : buffer ≠ 1) :
    ¬ (selectSlice (w := w) start count).Touches buffer := by
  have hc0 : ¬ (copySlice (w := w) 1 0 0 count).Touches buffer := fun ht => h0 (copySlice_touches _ _ _ _ _ ht)
  have hc1 : ¬ (copySlice (w := w) 0 1 start count).Touches buffer := fun ht => h1 (copySlice_touches _ _ _ _ _ ht)
  simp [selectSlice, Stmt.Touches, h0, h1, hc0, hc1]

theorem save_exec (cost : CostModel) (tape : RandomTape w) (buffer start count : Nat)
    (before : State w) (distinct : buffer ≠ 0)
    (span : start + count ≤ (before.bufs 0).size)
    (source_fits : (before.bufs 0).size < 2 ^ w)
    (capacities : ∀ b, before.caps b < 2 ^ w) :
    ∃ after elapsed net peak,
      Caliper.Exec cost tape (save buffer start count) before after elapsed net peak ∧
      (after.bufs buffer).toList = ((before.bufs 0).toList.drop start).take count ∧
      after.bufs 0 = before.bufs 0 ∧ after.regs 0 = before.regs 0 ∧
      (∀ b, after.caps b < 2 ^ w) := by
  let allocated := before.allocBuf buffer count
  have hc : count < 2 ^ w := lt_of_le_of_lt (by omega) source_fits
  obtain ⟨after, execution, contents, caps⟩ := copySlice_exec cost tape 0 buffer distinct count start allocated
    (by simpa [allocated, Ne.symm distinct] using span)
    (by simpa [allocated, Ne.symm distinct] using source_fits) (by simp [allocated])
  have he := Caliper.Exec.seq (Caliper.Exec.memAllocI (C := cost) (tape := tape)
      (s := before) (b := buffer) (n := count)) execution
  refine ⟨after, _, _, _, he, ?_, ?_, ?_, ?_⟩
  · simpa [allocated, Ne.symm distinct] using contents
  · exact he.frame_buf (by
      have ht : ¬ (copySlice (w := w) 0 buffer start count).Touches 0 :=
        fun h => distinct (copySlice_touches _ _ _ _ _ h).symm
      simp [Stmt.Touches, Ne.symm distinct, ht])
  · exact he.frame_reg (by simp [Stmt.Writes, copySlice_preserves_zero])
  · intro b
    rw [caps]
    change (if b = buffer then count else before.caps b) < 2 ^ w
    split_ifs <;> first | exact hc | exact capacities b

def restoreOperands (buffer outputWords savedWords : Nat) : List (Operand w) :=
  reads 0 0 outputWords ++ reads buffer 0 savedWords

def code (body : Stmt w) (buffer inputWords outputWords savedWords : Nat) : Stmt w :=
  save buffer inputWords savedWords ;;
  selectSlice 0 inputWords ;;
  body ;;
  Assembly.code (restoreOperands buffer outputWords savedWords) ;;
  .memFree buffer

end Retain

variable {A B S : Type} {cost : CostModel} {input : Representation w A} {output : Representation w B}
  {f : A → B}

/-- The finite mutation footprint determines a buffer the callee cannot clobber.
The chosen name must still fit the address width; no unbounded name is hidden. -/
def Realizer.savedBuffer (body : Realizer cost input output f) : Nat := max 2 body.code.memBound

def Realizer.retain (body : Realizer cost input output f) (allocation : 1 ≤ cost.allocPerWord)
    (saved : Representation w S) (hw : 16 < 2 ^ w)
    (name_fits : body.savedBuffer < 2 ^ w)
    (input_fits : input.encoding.words + saved.encoding.words < 2 ^ w)
    (output_fits : output.encoding.words + saved.encoding.words < 2 ^ w) :
    Realizer cost (input.prod saved input_fits) (output.prod saved output_fits)
      (fun value => (f value.1, value.2)) where
  code := Retain.code body.code body.savedBuffer input.encoding.words output.encoding.words saved.encoding.words
  positive_width := width_pos hw
  description_fits := by
    apply DescriptionFits.seq (width_pos hw) (Retain.save_descriptionFits _ _ _ hw name_fits saved.fits)
    apply DescriptionFits.seq (width_pos hw) (selectSlice_descriptionFits _ _ hw input.fits)
    apply DescriptionFits.seq (width_pos hw) body.description_fits
    apply DescriptionFits.seq (width_pos hw)
    · apply Assembly.code_descriptionFits _ hw
      · simpa [Retain.restoreOperands, reads_length] using output_fits
      · intro operand member
        rcases List.mem_append.mp member with left | right
        · exact reads_namesFit 0 0 _ (by positivity) operand left
        · exact reads_namesFit _ 0 _ name_fits operand right
    · simp [DescriptionFits, description, name_fits]; omega
  random_free := by simp [Retain.code, Stmt.RandomFree, Retain.save_randomFree,
    selectSlice_randomFree, body.random_free, Assembly.code_randomFree]
  time value := (Retain.save (w := w) body.savedBuffer input.encoding.words saved.encoding.words).staticTime cost +
    ((selectSlice (w := w) 0 input.encoding.words).staticTime cost +
      (body.time value.1 + ((Assembly.code (Retain.restoreOperands body.savedBuffer output.encoding.words saved.encoding.words)).staticTime cost + cost.memFree)))
  net value := (Retain.save (w := w) body.savedBuffer input.encoding.words saved.encoding.words).staticTime cost +
    ((selectSlice (w := w) 0 input.encoding.words).staticTime cost +
      (body.time value.1 + ((Assembly.code (Retain.restoreOperands body.savedBuffer output.encoding.words saved.encoding.words)).staticTime cost + cost.memFree)))
  workspace value := (Retain.save (w := w) body.savedBuffer input.encoding.words saved.encoding.words).staticTime cost +
    ((selectSlice (w := w) 0 input.encoding.words).staticTime cost +
      (body.time value.1 + ((Assembly.code (Retain.restoreOperands body.savedBuffer output.encoding.words saved.encoding.words)).staticTime cost + cost.memFree)))
  correct tape value before represented := by
    have h0 : body.savedBuffer ≠ 0 := by simp [savedBuffer]
    have h1 : body.savedBuffer ≠ 1 := by simp [savedBuffer]; omega
    have hin := represented_size (input.prod saved input_fits) represented
    have hs : (before.bufs 0).size < 2 ^ w := by rw [hin]; exact input_fits
    obtain ⟨stored, ts, ds, ps, es, savedContents, original, zero, capacities⟩ :=
      Retain.save_exec cost tape body.savedBuffer input.encoding.words saved.encoding.words before h0
        (by simpa [Representation.prod, Encoding.prod, Encoding.checked] using hin.ge) hs represented.2.2.2
    have hsTime := es.straight_time_eq (Retain.save_straight _ _ _)
    subst ts
    have savedValue : (stored.bufs body.savedBuffer).toList = saved.encoding.encode value.2 := by
      rw [savedContents, represented.2.1]
      change ((input.encoding.encode value.1 ++ saved.encoding.encode value.2).drop input.encoding.words).take saved.encoding.words = _
      rw [← input.encoding.encode_length value.1, ← saved.encoding.encode_length value.2]
      simp
    have storedInput : (input.prod saved input_fits).Holds value stored :=
      ⟨zero.trans represented.1, by rw [original]; exact represented.2.1,
        es.wellFormed_preserved represented.2.2.1, capacities⟩
    let projection := firstRealizer cost allocation input saved hw input_fits
    obtain ⟨projected, dp, pp, ep, projectedInput, _, _⟩ := projection.correct tape value stored storedInput
    have projectedSaved : (projected.bufs body.savedBuffer).toList = saved.encoding.encode value.2 := by
      rw [ep.frame_buf (Retain.select_untouched _ _ _ h0 h1), savedValue]
    obtain ⟨called, dc, pc, ec, calledOutput, _, _⟩ := body.correct tape value.1 projected projectedInput
    have untouched : ¬ body.code.Touches body.savedBuffer := by
      intro ht
      have bound := Stmt.touches_lt_memBound ht
      exact Nat.not_lt_of_ge (le_max_right 2 body.code.memBound) bound
    have calledSaved : (called.bufs body.savedBuffer).toList = saved.encoding.encode value.2 := by
      rw [ec.frame_buf untouched, projectedSaved]
    have savedSize : (called.bufs body.savedBuffer).size = saved.encoding.words := by
      have := congrArg List.length calledSaved
      simpa [saved.encoding.encode_length] using this
    let operands := Retain.restoreOperands (w := w) body.savedBuffer output.encoding.words saved.encoding.words
    have valid : Valid 1 called operands := by
      intro operand member
      rcases List.mem_append.mp member with left | right
      · exact reads_valid 1 0 0 _ called (by decide)
          (by simp [represented_size output calledOutput])
          (by rw [represented_size output calledOutput]; exact output.fits) operand left
      · exact reads_valid 1 _ 0 _ called h1 (by simp [savedSize])
          (by rw [savedSize]; exact saved.fits) operand right
    obtain ⟨rebuilt, tr, dr, pr, er, rebuiltContents, rebuiltZero, rebuiltCaps⟩ :=
      Assembly.code_exec cost tape operands called valid
        (by simpa [operands, Retain.restoreOperands, reads_length] using output_fits) calledOutput.2.2.2
    have hrTime := er.straight_time_eq (Assembly.code_straight operands)
    subst tr
    have rebuiltValue : (rebuilt.bufs 0).toList =
        (output.prod saved output_fits).encoding.encode (f value.1, value.2) := by
      rw [rebuiltContents]
      have left := reads_values 0 0 output.encoding.words called (by simp [represented_size output calledOutput])
      have right := reads_values body.savedBuffer 0 saved.encoding.words called (by simp [savedSize])
      change values (reads 0 0 output.encoding.words ++ reads body.savedBuffer 0 saved.encoding.words) called =
        output.encoding.encode (f value.1) ++ saved.encoding.encode value.2
      simp only [values, List.map_append] at *
      rw [left, right, List.drop_zero, List.drop_zero, calledOutput.2.1, calledSaved,
        ← output.encoding.encode_length (f value.1), ← saved.encoding.encode_length value.2]
      simp
    let after := rebuilt.allocBuf body.savedBuffer 0
    have execution := Caliper.Exec.seq es (Caliper.Exec.seq ep
      (Caliper.Exec.seq ec (Caliper.Exec.seq er (Caliper.Exec.memFree (b := body.savedBuffer)))))
    refine ⟨after, _, _, execution, ⟨?_, ?_, execution.wellFormed_preserved represented.2.2.1, ?_⟩,
      execution.net_le_time allocation, execution.peak_le_time allocation⟩
    · exact rebuiltZero.trans calledOutput.1
    · simpa [after, Ne.symm h0] using rebuiltValue
    · intro buffer
      change (if buffer = body.savedBuffer then 0 else rebuilt.caps buffer) < 2 ^ w
      split_ifs <;> first | positivity | exact rebuiltCaps buffer

/-- The wrapper's time is linear in input, output and retained payload sizes,
in addition to the actual callee time. -/
theorem Realizer.retain_time_unit_le {input : Representation w A} {output : Representation w B}
    {f : A → B} (body : Realizer .unit input output f)
    (saved : Representation w S) (hw : 16 < 2 ^ w) (name_fits : body.savedBuffer < 2 ^ w)
    (input_fits : input.encoding.words + saved.encoding.words < 2 ^ w)
    (output_fits : output.encoding.words + saved.encoding.words < 2 ^ w) (value : A × S) :
    (body.retain (by decide) saved hw name_fits input_fits output_fits).time value ≤
      body.time value.1 + 8 * input.encoding.words + 8 * output.encoding.words + 12 * saved.encoding.words := by
  have bound := Assembly.code_time_unit_le (Retain.restoreOperands (w := w) body.savedBuffer
    output.encoding.words saved.encoding.words)
  simp only [Retain.restoreOperands, List.length_append, reads_length] at bound
  simp only [CostModel.unit] at bound
  simp only [retain, Retain.save, Retain.restoreOperands, Stmt.staticTime, copySlice_staticTime, selectSlice_staticTime,
    sliceWordTime, CostModel.unit]
  omega

theorem Realizer.retain_descriptionWords_le (body : Realizer cost input output f)
    (allocation : 1 ≤ cost.allocPerWord) (saved : Representation w S) (hw : 16 < 2 ^ w)
    (name_fits : body.savedBuffer < 2 ^ w)
    (input_fits : input.encoding.words + saved.encoding.words < 2 ^ w)
    (output_fits : output.encoding.words + saved.encoding.words < 2 ^ w) :
    descriptionWords (body.retain allocation saved hw name_fits input_fits output_fits).code ≤
      descriptionWords body.code + 26 * input.encoding.words + 26 * output.encoding.words +
        39 * saved.encoding.words + 39 := by
  have bound := Assembly.code_descriptionWords_le (Retain.restoreOperands (w := w) body.savedBuffer
    output.encoding.words saved.encoding.words)
  simp only [Retain.restoreOperands, List.length_append, reads_length] at bound
  simp only [retain, Retain.code, Retain.restoreOperands, descriptionWords_seq, Retain.save_descriptionWords,
    selectSlice_descriptionWords]
  simp only [descriptionWords, description, List.length_cons, List.length_nil] at *
  omega

end Signatures.Runtime.CaliperBackend
