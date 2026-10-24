import Proofs.Runtime.Caliper.Wiring

/-! Construction of bounded layouts from literal words and indexed reads.
Every output word has executable instructions. Buffer 1 is scratch; the final
value is copied back to buffer 0 and scratch is released. Mathematical `values`
is only the specification of those instructions, not a host-language operation.
-/

namespace Signatures.Runtime.CaliperBackend.Assembly

open Caliper

variable {w : Nat}

inductive Operand (w : Nat) where
  | literal (word : Word w)
  | read (source : BufId) (offset : Nat)

def Operand.value (state : State w) : Operand w → Word w
  | .literal word => word
  | .read source offset => (state.bufs source)[offset]?.getD 0

def Operand.Valid (destination : BufId) (state : State w) : Operand w → Prop
  | .literal _ => True
  | .read source offset => source ≠ destination ∧ offset < (state.bufs source).size ∧ offset < 2 ^ w

def Operand.NamesFit : Operand w → Prop
  | .literal _ => True
  | .read source _ => source < 2 ^ w

def Operand.code (destination : BufId) : Operand w → Stmt w
  | .literal word => .imm 2 word ;; .memPush destination 2
  | .read source offset => .imm 1 (BitVec.ofNat w offset) ;;
      .memLoad 2 source 1 ;; .memPush destination 2

def emit (destination : BufId) : List (Operand w) → Stmt w
  | [] => .skip
  | operand :: rest => operand.code destination ;; emit destination rest

def Valid (destination : BufId) (state : State w) (operands : List (Operand w)) : Prop :=
  ∀ operand ∈ operands, operand.Valid destination state

def values (operands : List (Operand w)) (state : State w) : List (Word w) :=
  operands.map (Operand.value state)

def reads (source start : Nat) : Nat → List (Operand w)
  | 0 => []
  | count + 1 => .read source start :: reads source (start + 1) count

theorem reads_length (source start count : Nat) : (reads (w := w) source start count).length = count := by
  induction count generalizing start <;> simp [reads, *]

theorem reads_valid (destination source start count : Nat) (state : State w)
    (distinct : source ≠ destination) (span : start + count ≤ (state.bufs source).size)
    (fits : (state.bufs source).size < 2 ^ w) : Valid destination state (reads source start count) := by
  induction count generalizing start with
  | zero => simp [Valid, reads]
  | succ count ih =>
    simp only [Valid, reads, List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨distinct, by omega, by omega⟩, ih (start + 1) (by omega)⟩

theorem reads_values (source start count : Nat) (state : State w)
    (span : start + count ≤ (state.bufs source).size) :
    values (reads source start count) state = ((state.bufs source).toList.drop start).take count := by
  induction count generalizing start with
  | zero => simp [reads, values]
  | succ count ih =>
    have hi : start < (state.bufs source).size := by omega
    simp only [reads, values, List.map_cons, Operand.value]
    rw [show (reads source (start + 1) count).map (Operand.value state) =
      ((state.bufs source).toList.drop (start + 1)).take count from ih _ (by omega)]
    rw [List.drop_eq_getElem_cons (i := start) (l := (state.bufs source).toList) (by simpa using hi)]
    simp [hi]

theorem reads_namesFit (source start count : Nat) (fits : source < 2 ^ w) :
    ∀ operand ∈ reads source start count, Operand.NamesFit (w := w) operand := by
  induction count generalizing start with
  | zero => simp [reads]
  | succ count ih =>
    simp only [reads, List.mem_cons, forall_eq_or_imp]
    exact ⟨fits, ih _⟩

theorem emit_straight (destination : BufId) (operands : List (Operand w)) :
    (emit destination operands).Straight := by
  induction operands with
  | nil => trivial
  | cons operand rest ih => cases operand <;> simp [emit, Operand.code, Stmt.Straight, ih]

theorem emit_randomFree (destination : BufId) (operands : List (Operand w)) :
    (emit destination operands).RandomFree := by
  induction operands with
  | nil => trivial
  | cons operand rest ih => cases operand <;> simp [emit, Operand.code, Stmt.RandomFree, ih]

theorem emit_preserves_zero (destination : BufId) (operands : List (Operand w)) :
    ¬ (emit destination operands).Writes 0 := by
  induction operands with
  | nil => simp [emit]
  | cons operand rest ih => cases operand <;> simp [emit, Operand.code, Stmt.Writes, ih]

theorem emit_untouched (destination buffer : BufId) (operands : List (Operand w))
    (distinct : buffer ≠ destination) : ¬ (emit destination operands).Touches buffer := by
  induction operands with
  | nil => simp [emit]
  | cons operand rest ih => cases operand <;> simp [emit, Operand.code, Stmt.Touches, distinct, ih]

theorem emit_descriptionFits (destination : BufId) (operands : List (Operand w))
    (hw : 16 < 2 ^ w) (hd : destination < 2 ^ w)
    (names : ∀ operand ∈ operands, operand.NamesFit) : DescriptionFits (emit destination operands) := by
  have hp := (width_pos hw).ne'
  induction operands with
  | nil => simp [emit, DescriptionFits, description]
  | cons operand rest ih =>
    apply DescriptionFits.seq (width_pos hw)
    · have hn := names operand (by simp)
      cases operand with
      | literal word =>
        have hv := word.isLt
        simp [Operand.code, DescriptionFits, description, hp, hd]
        omega
      | read source offset =>
        have hv := (BitVec.ofNat w offset).isLt
        simp only [Operand.NamesFit] at hn
        simp [Operand.code, DescriptionFits, description, hp, hd, hn]
        omega
    · exact ih (fun operand member => names operand (by simp [member]))

private theorem valid_frame {destination : BufId} {before after : State w}
    (frame : ∀ source, source ≠ destination → after.bufs source = before.bufs source)
    {operand : Operand w} (valid : operand.Valid destination before) :
    operand.Valid destination after ∧ operand.value after = operand.value before := by
  cases operand with
  | literal word => exact ⟨trivial, rfl⟩
  | read source offset =>
    constructor
    · change source ≠ destination ∧ offset < (after.bufs source).size ∧ offset < 2 ^ w
      rw [frame source valid.1]
      exact valid
    · simp [Operand.value, frame source valid.1]

theorem emit_exec (cost : CostModel) (tape : RandomTape w) (destination : BufId)
    (operands : List (Operand w)) (before : State w) (valid : Valid destination before operands)
    (room : (before.bufs destination).size + operands.length ≤ before.caps destination) :
    ∃ after, Caliper.Exec cost tape (emit destination operands) before after
      ((emit destination operands).staticTime cost) 0 0 ∧
      (after.bufs destination).toList = (before.bufs destination).toList ++ values operands before ∧
      after.caps = before.caps := by
  induction operands generalizing before with
  | nil => exact ⟨before, .skip, by simp [values], rfl⟩
  | cons operand rest ih =>
    have hv := valid operand (by simp)
    have hp : (before.bufs destination).size < before.caps destination := by simp only [List.length_cons] at room; omega
    have one : ∃ middle, Caliper.Exec cost tape (operand.code destination) before middle
        ((operand.code destination).staticTime cost) 0 0 ∧
        middle.bufs destination = (before.bufs destination).push (operand.value before) ∧
        middle.caps = before.caps := by
      cases operand with
      | literal word =>
        refine ⟨(before.setReg 2 word).setBuf destination ((before.bufs destination).push word), ?_, ?_, rfl⟩
        · simpa [Operand.code, Stmt.staticTime] using
            (Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := before) (d := 2) (v := word))
              (Caliper.Exec.memPush (b := destination) (src := 2) hp))
        · simp [Operand.value]
      | read source offset =>
        have hindex : offset < (before.bufs source).size := hv.2.1
        have hi : (BitVec.ofNat w offset).toNat = offset := by simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv.2.2]
        have hl : ((before.setReg 1 (BitVec.ofNat w offset)).regs 1).toNat <
            ((before.setReg 1 (BitVec.ofNat w offset)).bufs source).size := by simpa [hi] using hv.2.1
        refine ⟨((before.setReg 1 (BitVec.ofNat w offset)).setReg 2 (before.bufs source)[offset]).setBuf
          destination ((before.bufs destination).push (before.bufs source)[offset]), ?_, ?_, rfl⟩
        · simpa [Operand.code, Stmt.staticTime, hi] using
            Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := before) (d := 1) (v := BitVec.ofNat w offset))
              (Caliper.Exec.seq (Caliper.Exec.memLoad (d := 2) hl)
                (Caliper.Exec.memPush (b := destination) (src := 2) hp))
        · simp [Operand.value, hv.2.1]
    obtain ⟨middle, he, hb, hc⟩ := one
    have frame : ∀ source, source ≠ destination → middle.bufs source = before.bufs source := by
      intro source distinct
      apply he.frame_buf
      cases operand <;> simp [Operand.code, Stmt.Touches, distinct]
    have vr : Valid destination middle rest := fun op member =>
      (valid_frame frame (valid op (by simp [member]))).1
    have vv : values rest middle = values rest before := by
      apply List.map_congr_left
      intro op member
      exact (valid_frame frame (valid op (by simp [member]))).2
    obtain ⟨after, her, hbr, hcr⟩ := ih middle vr (by rw [hb, hc]; simp only [Array.size_push]; simp only [List.length_cons] at room; omega)
    refine ⟨after, by simpa [emit, Stmt.staticTime] using Caliper.Exec.seq he her, ?_, hcr.trans hc⟩
    rw [hbr, hb, Array.toList_push, vv]
    simp [values, List.append_assoc]

def code (operands : List (Operand w)) : Stmt w :=
  .memAllocI 1 operands.length ;;
  emit 1 operands ;;
  .memAllocI 0 operands.length ;;
  copySlice 1 0 0 operands.length ;;
  .memFree 1

theorem code_straight (operands : List (Operand w)) : (code operands).Straight := by
  simp [code, Stmt.Straight, emit_straight, copySlice_straight]

theorem code_randomFree (operands : List (Operand w)) : (code operands).RandomFree := by
  simp [code, Stmt.RandomFree, emit_randomFree, copySlice_randomFree]

theorem code_descriptionFits (operands : List (Operand w)) (hw : 16 < 2 ^ w)
    (fits : operands.length < 2 ^ w) (names : ∀ operand ∈ operands, operand.NamesFit) :
    DescriptionFits (code operands) := by
  have hp := (width_pos hw).ne'
  apply DescriptionFits.seq (width_pos hw) (by simp [DescriptionFits, description, hp, fits]; omega)
  apply DescriptionFits.seq (width_pos hw)
    (emit_descriptionFits 1 operands hw (Nat.one_lt_two_pow (width_pos hw).ne') names)
  apply DescriptionFits.seq (width_pos hw) (by simp [DescriptionFits, description, fits]; omega)
  apply DescriptionFits.seq (width_pos hw) (copySlice_descriptionFits 1 0 0 _ hw (by omega) (by positivity))
  simp [DescriptionFits, description, hp]; omega

theorem emit_time_unit_le (destination : BufId) (operands : List (Operand w)) :
    (emit destination operands).staticTime .unit ≤ 3 * operands.length := by
  induction operands with
  | nil => simp [emit, Stmt.staticTime]
  | cons operand rest ih =>
    simp only [CostModel.unit] at ih
    cases operand <;> simp [emit, Operand.code, Stmt.staticTime, CostModel.unit] <;> omega

theorem code_time_unit_le (operands : List (Operand w)) :
    (code operands).staticTime .unit ≤ 8 * operands.length := by
  have := emit_time_unit_le 1 operands
  simp only [CostModel.unit] at this
  simp [code, Stmt.staticTime, copySlice_staticTime, sliceWordTime, CostModel.unit]
  omega

theorem emit_descriptionWords_le (destination : BufId) (operands : List (Operand w)) :
    descriptionWords (emit destination operands) ≤ 13 * operands.length + 1 := by
  induction operands with
  | nil => rfl
  | cons operand rest ih =>
    cases operand <;> simp only [emit, Operand.code, descriptionWords_seq, List.length_cons] <;>
      simp only [descriptionWords, description, List.length_cons, List.length_nil] at * <;> omega

theorem code_descriptionWords_le (operands : List (Operand w)) :
    descriptionWords (code operands) ≤ 26 * operands.length + 14 := by
  have := emit_descriptionWords_le 1 operands
  simp only [code, descriptionWords_seq, copySlice_descriptionWords]
  simp only [descriptionWords, description, List.length_cons, List.length_nil] at *
  omega

/-- Construction allocates and fills scratch, copies the result back, and frees
scratch. All reads are justified by the supplied source spans. -/
theorem code_exec (cost : CostModel) (tape : RandomTape w) (operands : List (Operand w))
    (before : State w) (valid : Valid 1 before operands) (fits : operands.length < 2 ^ w)
    (capacities : ∀ buffer, before.caps buffer < 2 ^ w) :
    ∃ after elapsed net peak, Caliper.Exec cost tape (code operands) before after elapsed net peak ∧
      (after.bufs 0).toList = values operands before ∧ after.regs 0 = before.regs 0 ∧
      (∀ buffer, after.caps buffer < 2 ^ w) := by
  let allocated := before.allocBuf 1 operands.length
  have frame : ∀ source, source ≠ 1 → allocated.bufs source = before.bufs source := by
    intro source distinct; simp [allocated, distinct]
  have va : Valid 1 allocated operands := fun op member => (valid_frame frame (valid op member)).1
  have vv : values operands allocated = values operands before := by
    apply List.map_congr_left
    intro op member
    exact (valid_frame frame (valid op member)).2
  obtain ⟨middle, he₁, hb₁, hc₁⟩ := emit_exec cost tape 1 operands allocated va (by simp [allocated])
  have hm : (middle.bufs 1).toList = values operands before := by simpa [allocated, vv] using hb₁
  have hms : (middle.bufs 1).size = operands.length := by
    have := congrArg List.length hm
    simpa [values] using this
  let reset := middle.allocBuf 0 operands.length
  obtain ⟨last, he₂, hb₂, hc₂⟩ := copySlice_exec cost tape 1 0 (by decide) operands.length 0 reset
    (by simp [reset, hms]) (by simpa [reset, hms] using fits) (by simp [reset])
  have execution := Caliper.Exec.seq (Caliper.Exec.memAllocI (C := cost) (tape := tape)
      (s := before) (b := 1) (n := operands.length))
    (Caliper.Exec.seq he₁ (Caliper.Exec.seq (Caliper.Exec.memAllocI (b := 0) (n := operands.length))
      (Caliper.Exec.seq he₂ (Caliper.Exec.memFree (b := 1)))))
  refine ⟨last.allocBuf 1 0, _, _, _, execution, ?_, ?_, ?_⟩
  · simp only [bufs_allocBuf_ne _ _ (by decide : (0 : Nat) ≠ 1)]
    have ht : (middle.bufs 1).toList.take operands.length = (middle.bufs 1).toList :=
      List.take_of_length_le (by simpa using le_of_eq hms)
    have hl : (last.bufs 0).toList = (middle.bufs 1).toList := by simpa [reset, ht] using hb₂
    exact hl.trans hm
  · exact execution.frame_reg (by simp [Stmt.Writes, emit_preserves_zero, copySlice_preserves_zero])
  · intro buffer
    change (if buffer = 1 then 0 else last.caps buffer) < 2 ^ w
    rw [hc₂]
    simp only [reset, State.allocBuf]
    rw [hc₁]
    simp only [allocated, State.allocBuf]
    split_ifs <;> first | exact fits | exact capacities buffer | positivity

theorem represented_size {A : Type} (input : Representation w A) {value : A} {state : State w}
    (represented : input.Holds value state) : (state.bufs 0).size = input.encoding.words := by
  have := congrArg List.length represented.2.1
  simpa [input.encoding.encode_length] using this

/-- A construction is a local realizer only after its concrete reads and output
layout are proved correct for every represented input. -/
def realizer {A B : Type} (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (input : Representation w A) (output : Representation w B) (f : A → B)
    (operands : List (Operand w)) (hw : 16 < 2 ^ w)
    (length : operands.length = output.encoding.words)
    (names : ∀ operand ∈ operands, operand.NamesFit)
    (valid : ∀ value state, input.Holds value state → Valid 1 state operands)
    (encoded : ∀ value state, input.Holds value state → values operands state = output.encoding.encode (f value)) :
    Realizer cost input output f where
  code := code operands
  positive_width := width_pos hw
  description_fits := code_descriptionFits operands hw (by rw [length]; exact output.fits) names
  random_free := code_randomFree operands
  time _ := (code operands).staticTime cost
  net _ := (code operands).staticTime cost
  workspace _ := (code operands).staticTime cost
  correct tape value before represented := by
    obtain ⟨after, elapsed, net, peak, execution, hout, hr, hc⟩ := code_exec cost tape operands before
      (valid value before represented) (by rw [length]; exact output.fits) represented.2.2.2
    have ht := execution.straight_time_eq (code_straight operands)
    subst elapsed
    exact ⟨after, net, peak, execution,
      ⟨hr.trans represented.1, hout.trans (encoded value before represented),
        execution.wellFormed_preserved represented.2.2.1, hc⟩,
      execution.net_le_time allocation, execution.peak_le_time allocation⟩

end Signatures.Runtime.CaliperBackend.Assembly
