import Proofs.Runtime.Caliper.ListConstruct
import Proofs.Runtime.Caliper.Branch

/-! Executed list case analysis. The branch tests the stored length. The empty
case builds the canonical empty tag and padding; the nonempty case copies the
head and tail and decrements the stored tail length. -/

namespace Signatures.Runtime.CaliperBackend.ListDestruct

open Caliper Assembly

variable {w : Nat} {A : Type}

def outputWords (entryWords capacity : Nat) : Nat := 2 + (capacity + 1) * entryWords

def operands (entryWords capacity : Nat) : List (Operand w) :=
  .literal 1 :: (reads 0 1 entryWords ++ reads 0 0 1 ++ reads 0 (1 + entryWords) (capacity * entryWords))

theorem operands_length (entryWords capacity : Nat) :
    (operands (w := w) entryWords capacity).length = outputWords entryWords capacity := by
  simp [operands, reads_length, outputWords]; ring

theorem operands_names (entryWords capacity : Nat) :
    ∀ operand ∈ operands (w := w) entryWords capacity, operand.NamesFit := by
  intro operand member
  simp only [operands, List.mem_cons, List.mem_append] at member
  rcases member with rfl | (member | member) | member
  · trivial
  all_goals exact reads_namesFit 0 _ _ (by positivity) operand member

theorem operands_valid (entryWords capacity : Nat) (before : State w)
    (size : (before.bufs 0).size = 1 + (capacity + 1) * entryWords)
    (fits : (before.bufs 0).size < 2 ^ w) : Valid 1 before (operands entryWords capacity) := by
  intro operand member
  simp only [operands, List.mem_cons, List.mem_append] at member
  rcases member with rfl | (member | member) | member
  · trivial
  all_goals exact reads_valid 1 0 _ _ before (by decide) (by rw [size]; nlinarith) fits operand member

theorem operands_values (head payload : List (Word w)) (length : Word w)
    (capacity : Nat) (payloadSize : payload.length = capacity * head.length)
    (before : State w) (contents : (before.bufs 0).toList = length :: (head ++ payload)) :
    values (operands head.length capacity) before = 1 :: (head ++ length :: payload) := by
  have size := congrArg List.length contents
  simp only [Array.length_toList, List.length_append, List.length_cons, payloadSize] at size
  have h₁ := reads_values (w := w) 0 1 head.length before (by omega)
  have h₂ := reads_values (w := w) 0 0 1 before (by omega)
  have h₃ := reads_values (w := w) 0 (1 + head.length) (capacity * head.length) before (by omega)
  simp only [operands, values, List.map_cons, List.map_append, Operand.value]
  change 1 :: (values (reads 0 1 head.length) before ++ values (reads 0 0 1) before ++
    values (reads 0 (1 + head.length) (capacity * head.length)) before) = _
  rw [h₁, h₂, h₃, contents, ← payloadSize]
  simp [Nat.add_comm 1]

def nonemptyCode (entryWords capacity : Nat) : Stmt w :=
  Assembly.code (operands entryWords capacity) ;; CellArithmetic.code (1 + entryWords) .sub 1

def emptyCode (entryWords capacity : Nat) : Stmt w :=
  Assembly.code (List.replicate (outputWords entryWords capacity) (.literal 0))

def code (entryWords capacity : Nat) : Stmt w :=
  .memLoad 1 0 0 ;; .ifNZ 1 (nonemptyCode entryWords capacity) (emptyCode entryWords capacity)

theorem nonemptyCode_straight (entryWords capacity : Nat) : (nonemptyCode (w := w) entryWords capacity).Straight :=
  ⟨code_straight _, CellArithmetic.straight _ _ _⟩

theorem code_randomFree (entryWords capacity : Nat) : (code (w := w) entryWords capacity).RandomFree := by
  simp [code, nonemptyCode, emptyCode, Stmt.RandomFree, Assembly.code_randomFree, CellArithmetic.randomFree]

theorem code_descriptionFits (entryWords capacity : Nat) (hw : 16 < 2 ^ w)
    (fits : outputWords entryWords capacity < 2 ^ w) : DescriptionFits (code (w := w) entryWords capacity) := by
  have positive := (width_pos hw).ne'
  have hn : DescriptionFits (nonemptyCode (w := w) entryWords capacity) :=
    DescriptionFits.seq (width_pos hw)
      (Assembly.code_descriptionFits _ hw (by rw [operands_length]; exact fits) (operands_names _ _))
      (CellArithmetic.descriptionFits _ _ _ hw)
  have he : DescriptionFits (emptyCode (w := w) entryWords capacity) :=
    Assembly.code_descriptionFits _ hw (by simpa using fits) (by
      intro operand member; simp only [List.mem_replicate] at member; rcases member with ⟨_, rfl⟩; trivial)
  apply DescriptionFits.seq (width_pos hw) (by simp [DescriptionFits, description, positive]; omega)
  intro token member
  simp only [description, List.mem_cons, List.mem_append] at member
  rcases member with rfl | rfl | member | member
  · omega
  · exact Nat.one_lt_two_pow positive
  · exact hn token member
  · exact he token member

theorem nonempty_exec (cost : CostModel) (tape : RandomTape w)
    (head payload : List (Word w)) (length : Word w) (capacity : Nat)
    (payloadSize : payload.length = capacity * head.length)
    (before : State w) (contents : (before.bufs 0).toList = length :: (head ++ payload))
    (fits : outputWords head.length capacity < 2 ^ w)
    (capacities : ∀ buffer, before.caps buffer < 2 ^ w) :
    ∃ after elapsed net peak,
      Caliper.Exec cost tape (nonemptyCode head.length capacity) before after elapsed net peak ∧
      (after.bufs 0).toList = 1 :: (head ++ (length - 1) :: payload) ∧
      after.regs 0 = before.regs 0 ∧ (∀ buffer, after.caps buffer < 2 ^ w) := by
  have size : (before.bufs 0).size = 1 + (capacity + 1) * head.length := by
    have size := congrArg List.length contents
    simp only [Array.length_toList, List.length_append, List.length_cons, payloadSize] at size
    nlinarith
  obtain ⟨middle, time, net, peak, copied, stored, zero, caps⟩ := Assembly.code_exec cost tape
    (operands head.length capacity) before
    (operands_valid _ _ before size (by rw [size]; dsimp [outputWords] at fits; omega))
    (by rw [operands_length]; exact fits) capacities
  rw [operands_values head payload length capacity payloadSize before contents] at stored
  obtain ⟨after, decremented, result, offset, finalCaps⟩ :=
    CellArithmetic.exec_at cost tape (1 :: head) payload length 1 .sub middle stored (by
      simp only [List.length_cons]
      dsimp [outputWords] at fits
      nlinarith)
  have execution := Caliper.Exec.seq copied decremented
  refine ⟨after, time + (CellArithmetic.code (1 + head.length) .sub (1 : Word w)).staticTime cost,
    net + 0, max peak (net + 0), ?_, result, offset.trans zero, ?_⟩
  · simpa [nonemptyCode, Nat.add_comm 1] using execution
  · intro buffer; rw [finalCaps]; exact caps buffer

theorem empty_exec (cost : CostModel) (tape : RandomTape w) (entryWords capacity : Nat)
    (before : State w) (fits : outputWords entryWords capacity < 2 ^ w)
    (capacities : ∀ buffer, before.caps buffer < 2 ^ w) :
    ∃ after elapsed net peak,
      Caliper.Exec cost tape (emptyCode entryWords capacity) before after elapsed net peak ∧
      (after.bufs 0).toList = List.replicate (outputWords entryWords capacity) 0 ∧
      after.regs 0 = before.regs 0 ∧ (∀ buffer, after.caps buffer < 2 ^ w) := by
  obtain ⟨after, elapsed, net, peak, execution, stored, zero, caps⟩ := Assembly.code_exec cost tape
    (List.replicate (outputWords entryWords capacity) (.literal 0)) before
    (by intro operand member; simp only [List.mem_replicate] at member; rcases member with ⟨_, rfl⟩; trivial)
    (by simpa using fits) capacities
  exact ⟨after, elapsed, net, peak, execution, by simpa [values, Operand.value] using stored, zero, caps⟩

end Signatures.Runtime.CaliperBackend.ListDestruct
