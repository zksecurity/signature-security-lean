import Signatures.Runtime.Caliper.Resources
import Signatures.Runtime.Caliper.FoldStep
import Signatures.Runtime.Caliper.Pairing

/-! Dense register and descriptor bounds for generated code. A word-sized name
can still be very large: description length alone is not a bound on its value.
Primitive routines supply a name bound. Generated wrappers add at most their
stored-code size to this reservation, including fresh saved-buffer names. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

structure NamesBound (code : Stmt w) (slots : Nat) : Prop where
  registers : registerSlots code ≤ slots
  buffers : code.memBound ≤ slots

/-- Compiler-generated names fit within the primitive reservation plus the
stored-code count. This property is proved for the compiler, not arbitrary code. -/
def NamesAccounted (code : Stmt w) (primitiveSlots : Nat) : Prop :=
  NamesBound code (primitiveSlots + descriptionWords code)

theorem NamesBound.mono {code : Stmt w} {a b : Nat} (bound : NamesBound code a)
    (larger : a ≤ b) : NamesBound code b :=
  ⟨bound.registers.trans larger, bound.buffers.trans larger⟩

theorem NamesBound.accounted {code : Stmt w} {slots : Nat} (bound : NamesBound code slots) :
    NamesAccounted code slots := bound.mono (Nat.le_add_right _ _)

theorem NamesAccounted.mono {code : Stmt w} {a b : Nat} (bound : NamesAccounted code a)
    (larger : a ≤ b) : NamesAccounted code b := NamesBound.mono bound (Nat.add_le_add_right larger _)

theorem NamesAccounted.seq {first second : Stmt w} {slots : Nat}
    (left : NamesAccounted first slots) (right : NamesAccounted second slots) :
    NamesAccounted (first ;; second) slots := by
  rcases left with ⟨lr, lb⟩
  rcases right with ⟨rr, rb⟩
  constructor <;> simp only [registerSlots, Stmt.memBound, descriptionWords_seq] <;> omega

theorem NamesAccounted.ifNZ {yes no : Stmt w} {slots : Nat}
    (left : NamesAccounted yes slots) (right : NamesAccounted no slots) :
    NamesAccounted (.ifNZ 1 yes no) slots := by
  have words : descriptionWords (.ifNZ 1 yes no) = descriptionWords yes + descriptionWords no + 2 := by
    simp [descriptionWords, description]
  rcases left with ⟨lr, lb⟩
  rcases right with ⟨rr, rb⟩
  constructor <;> simp only [registerSlots, Stmt.memBound, words] <;> omega

theorem skip_names (slots : Nat) : NamesAccounted (.skip : Stmt w) slots :=
  (show NamesBound (.skip : Stmt w) slots from ⟨Nat.zero_le _, Nat.zero_le _⟩).accounted

theorem loadTag_names (slots : Nat) : NamesAccounted (.memLoad 1 0 0 : Stmt w) slots := by
  constructor <;> simp [registerSlots, Stmt.memBound, descriptionWords, description]

theorem copySlice_names (source destination start count : Nat) :
    registerSlots (copySlice (w := w) source destination start count) ≤ 3 ∧
    (copySlice (w := w) source destination start count).memBound ≤ max (source + 1) (destination + 1) := by
  induction count generalizing start with
  | zero => simp [copySlice, registerSlots, Stmt.memBound]
  | succ count ih =>
    have previous := ih (start + 1)
    simp only [copySlice, registerSlots, Stmt.memBound]
    omega

theorem selectSlice_names (start count slots : Nat) :
    NamesAccounted (selectSlice (w := w) start count) slots := by
  have first := copySlice_names (w := w) 0 1 start count
  have second := copySlice_names (w := w) 1 0 0 count
  constructor <;> rw [selectSlice_descriptionWords] <;>
    simp only [selectSlice, registerSlots, Stmt.memBound] <;> omega

namespace Assembly

def Operand.SourcesBound (slots : Nat) : Operand w → Prop
  | .literal _ => True
  | .read source _ => source + 1 ≤ slots

def SourcesBound (operands : List (Operand w)) (slots : Nat) : Prop :=
  ∀ operand ∈ operands, operand.SourcesBound slots

theorem sourcesBound_reads (source start count slots : Nat) (bound : source + 1 ≤ slots) :
    SourcesBound (reads (w := w) source start count) slots := by
  induction count generalizing start with
  | zero => simp [SourcesBound, reads]
  | succ count ih =>
    simpa only [SourcesBound, reads, List.mem_cons, forall_eq_or_imp, Operand.SourcesBound] using
      And.intro bound (ih (start + 1))

@[simp] theorem sourcesBound_append (left right : List (Operand w)) (slots : Nat) :
    SourcesBound (left ++ right) slots ↔ SourcesBound left slots ∧ SourcesBound right slots := by
  simp [SourcesBound, List.mem_append, or_imp, forall_and]

@[simp] theorem sourcesBound_nil (slots : Nat) : SourcesBound ([] : List (Operand w)) slots := by
  simp [SourcesBound]

@[simp] theorem sourcesBound_literal (word : Word w) (operands : List (Operand w)) (slots : Nat) :
    SourcesBound (.literal word :: operands) slots ↔ SourcesBound operands slots := by
  simp [SourcesBound, Operand.SourcesBound]

theorem sourcesBound_replicate (word : Word w) (count slots : Nat) :
    SourcesBound (List.replicate count (.literal word)) slots := by
  intro operand member
  obtain rfl := List.eq_of_mem_replicate member
  trivial

theorem emit_names (destination : Nat) (operands : List (Operand w)) (slots : Nat)
    (sources : SourcesBound operands slots) :
    registerSlots (emit destination operands) ≤ 3 ∧
      (emit destination operands).memBound ≤ max (destination + 1) slots := by
  induction operands with
  | nil => simp [emit, registerSlots, Stmt.memBound]
  | cons operand rest ih =>
    have current := sources operand (by simp)
    change Operand.SourcesBound slots operand at current
    have following := ih (fun value member => sources value (by simp [member]))
    cases operand with
    | literal word =>
      simp only [emit, Operand.code, registerSlots, Stmt.memBound]
      omega
    | read source offset =>
      change source + 1 ≤ slots at current
      constructor
      · simp only [emit, Operand.code, registerSlots]
        omega
      · exact max_le (max_le (Nat.zero_le _)
          (max_le (current.trans (Nat.le_max_right _ _)) (Nat.le_max_left _ _))) following.2

theorem code_names (operands : List (Operand w)) (slots : Nat)
    (sources : SourcesBound operands slots) :
    registerSlots (code operands) ≤ 3 ∧ (code operands).memBound ≤ max 2 slots := by
  have emitted := emit_names 1 operands slots sources
  have copied := copySlice_names (w := w) 1 0 0 operands.length
  constructor <;> simp only [code, registerSlots, Stmt.memBound] <;> omega

theorem code_words_lower (operands : List (Operand w)) : 3 ≤ descriptionWords (code operands) := by
  simp only [code, descriptionWords_seq]
  simp only [descriptionWords, description, List.length_cons, List.length_nil]
  omega

theorem code_namesAccounted (operands : List (Operand w)) (slots : Nat)
    (sources : SourcesBound operands 1) : NamesAccounted (code operands) slots := by
  have bounds := code_names operands 1 sources
  have words := code_words_lower operands
  constructor <;> omega

end Assembly

theorem CellArithmetic.names (offset : Nat) (op : BinOp) (operand : Word w) (slots : Nat) :
    NamesAccounted (CellArithmetic.code offset op operand) slots := by
  constructor <;> rw [CellArithmetic.descriptionWords_eq] <;>
    simp only [CellArithmetic.code, registerSlots, Stmt.memBound] <;> omega

theorem Retain.code_names (body : Stmt w) (buffer input output saved : Nat)
    (reserved : 2 ≤ buffer) (bodyBound : body.memBound ≤ buffer) :
    registerSlots (Retain.code body buffer input output saved) ≤ max 3 (registerSlots body) ∧
      (Retain.code body buffer input output saved).memBound ≤ buffer + 1 := by
  have savedNames := copySlice_names (w := w) 0 buffer input saved
  have sources : Assembly.SourcesBound (Retain.restoreOperands (w := w) buffer output saved) (buffer + 1) := by
    exact (Assembly.sourcesBound_append _ _ _).mpr
      ⟨Assembly.sourcesBound_reads _ _ _ _ (by omega), Assembly.sourcesBound_reads _ _ _ _ (by omega)⟩
  have restored := Assembly.code_names _ _ sources
  have selectedNames : registerSlots (selectSlice (w := w) 0 input) ≤ 3 ∧
      (selectSlice (w := w) 0 input).memBound ≤ 2 := by
    have first := copySlice_names (w := w) 0 1 0 input
    have second := copySlice_names (w := w) 1 0 0 input
    simp only [selectSlice, registerSlots, Stmt.memBound]
    omega
  simp only [Retain.code, Retain.save, registerSlots, Stmt.memBound]
  omega

theorem Retain.names {body : Stmt w} {slots : Nat} (bound : NamesAccounted body slots)
    (input output saved : Nat) :
    NamesAccounted (Retain.code body (max 2 body.memBound) input output saved) slots := by
  have names := Retain.code_names body (max 2 body.memBound) input output saved
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have words : descriptionWords body + 4 ≤
      descriptionWords (Retain.code body (max 2 body.memBound) input output saved) := by
    simp only [Retain.code, descriptionWords_seq]
    omega
  rcases bound with ⟨registers, buffers⟩
  constructor <;> omega

end Signatures.Runtime.CaliperBackend
