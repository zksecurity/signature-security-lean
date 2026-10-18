import Signatures.Runtime.Caliper.SourceLists

/-! Executable frame construction for list folds. The input contains the list,
accumulator and environment. The prepared frame contains the body arguments and
a separately retained tail/environment; all copies and the tail-count update
are ordinary Caliper instructions. -/

namespace Signatures.Runtime.CaliperBackend.ListFold

open Caliper Assembly

variable {w : Nat}

theorem reads_block (leading chunk trailing : List (Word w)) (before : State w)
    (contents : (before.bufs 0).toList = leading ++ chunk ++ trailing) :
    values (reads 0 leading.length chunk.length) before = chunk := by
  have size := congrArg List.length contents
  simp only [Array.length_toList, List.length_append] at size
  rw [reads_values 0 _ _ before (by omega), contents, List.append_assoc]
  simp

def prepareWords (entry state env capacity : Nat) : Nat := 1 + (capacity + 1) * entry + state + 2 * env

def prepareOperands (entry state env capacity : Nat) : List (Operand w) :=
  reads 0 1 entry ++ reads 0 (1 + (capacity + 1) * entry) (state + env) ++
  reads 0 0 1 ++ reads 0 (1 + entry) (capacity * entry) ++
  reads 0 (1 + (capacity + 1) * entry + state) env

theorem prepareOperands_length (entry state env capacity : Nat) :
    (prepareOperands (w := w) entry state env capacity).length = prepareWords entry state env capacity := by
  simp [prepareOperands, reads_length, prepareWords]
  ring

theorem prepareOperands_names (entry state env capacity : Nat) :
    ∀ operand ∈ prepareOperands (w := w) entry state env capacity, operand.NamesFit := by
  intro operand member
  simp only [prepareOperands, List.mem_append] at member
  rcases member with (((member | member) | member) | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

theorem prepareOperands_valid (entry state env capacity : Nat) (before : State w)
    (size : (before.bufs 0).size = 1 + (capacity + 1) * entry + state + env)
    (fits : (before.bufs 0).size < 2 ^ w) : Valid 1 before (prepareOperands entry state env capacity) := by
  intro operand member
  simp only [prepareOperands, List.mem_append] at member
  rcases member with (((member | member) | member) | member) | member <;>
    exact reads_valid 1 0 _ _ before (by decide) (by rw [size] <;> nlinarith) fits operand member

theorem prepareOperands_values (head tail state env : List (Word w)) (count : Word w) (capacity : Nat)
    (tailSize : tail.length = capacity * head.length) (before : State w)
    (contents : (before.bufs 0).toList = count :: (head ++ tail ++ state ++ env)) :
    values (prepareOperands head.length state.length env.length capacity) before =
      (head ++ state ++ env) ++ count :: (tail ++ env) := by
  have first := reads_block [count] head (tail ++ state ++ env) before (by simpa [List.append_assoc] using contents)
  have argument := reads_block (count :: (head ++ tail)) (state ++ env) [] before (by simpa [List.append_assoc] using contents)
  have header := reads_block [] [count] (head ++ tail ++ state ++ env) before contents
  have rest := reads_block (count :: head) tail (state ++ env) before (by simpa [List.append_assoc] using contents)
  have saved := reads_block (count :: (head ++ tail ++ state)) env [] before (by simpa [List.append_assoc] using contents)
  have length : (count :: (head ++ tail)).length = 1 + (capacity + 1) * head.length := by
    simp only [List.length_cons, List.length_append, tailSize]
    ring
  have envOffset : (count :: (head ++ tail ++ state)).length = 1 + (capacity + 1) * head.length + state.length := by
    simp only [List.length_cons, List.length_append, tailSize]
    ring
  simp only [List.length_nil, List.length_cons] at first header rest
  rw [length, List.length_append] at argument
  rw [envOffset] at saved
  simp only [prepareOperands, values, List.map_append]
  change values (reads 0 1 head.length) before ++ values (reads 0 (1 + (capacity + 1) * head.length) (state.length + env.length)) before ++
    values (reads 0 0 1) before ++ values (reads 0 (1 + head.length) (capacity * head.length)) before ++
    values (reads 0 (1 + (capacity + 1) * head.length + state.length) env.length) before = _
  rw [first, argument, header, ← tailSize, Nat.add_comm 1 head.length, rest, saved]
  simp [List.append_assoc]

def prepare (entry state env capacity : Nat) : Stmt w :=
  Assembly.code (prepareOperands entry state env capacity) ;; CellArithmetic.code (entry + state + env) .sub 1

theorem prepare_straight (entry state env capacity : Nat) : (prepare (w := w) entry state env capacity).Straight :=
  ⟨Assembly.code_straight _, CellArithmetic.straight _ _ _⟩

theorem prepare_randomFree (entry state env capacity : Nat) : (prepare (w := w) entry state env capacity).RandomFree :=
  ⟨Assembly.code_randomFree _, CellArithmetic.randomFree _ _ _⟩

theorem prepare_descriptionFits (entry state env capacity : Nat) (hw : 16 < 2 ^ w)
    (fits : prepareWords entry state env capacity < 2 ^ w) : DescriptionFits (prepare (w := w) entry state env capacity) :=
  DescriptionFits.seq (width_pos hw)
    (Assembly.code_descriptionFits _ hw (by rw [prepareOperands_length]; exact fits) (prepareOperands_names _ _ _ _))
    (CellArithmetic.descriptionFits _ _ _ hw)

theorem prepare_exec (cost : CostModel) (tape : RandomTape w)
    (head tail state env : List (Word w)) (count : Nat) (capacity : Nat)
    (tailSize : tail.length = capacity * head.length) (before : State w)
    (contents : (before.bufs 0).toList = BitVec.ofNat w (count + 1) :: (head ++ tail ++ state ++ env))
    (fits : prepareWords head.length state.length env.length capacity < 2 ^ w)
    (capacities : ∀ buffer, before.caps buffer < 2 ^ w) :
    ∃ after elapsed net peak,
      Caliper.Exec cost tape (prepare head.length state.length env.length capacity) before after elapsed net peak ∧
      (after.bufs 0).toList = (head ++ state ++ env) ++ BitVec.ofNat w count :: (tail ++ env) ∧
      after.regs 0 = before.regs 0 ∧ (∀ buffer, after.caps buffer < 2 ^ w) := by
  have size : (before.bufs 0).size = 1 + (capacity + 1) * head.length + state.length + env.length := by
    have size := congrArg List.length contents
    simp only [Array.length_toList, List.length_cons, List.length_append, tailSize] at size
    nlinarith
  obtain ⟨middle, time, net, peak, copied, stored, zero, caps⟩ := Assembly.code_exec cost tape
    (prepareOperands head.length state.length env.length capacity) before
    (prepareOperands_valid _ _ _ _ before size (by rw [size]; dsimp [prepareWords] at fits; omega))
    (by rw [prepareOperands_length]; exact fits) capacities
  rw [prepareOperands_values head tail state env _ capacity tailSize before contents] at stored
  obtain ⟨after, decremented, result, offset, finalCaps⟩ :=
    CellArithmetic.exec_at cost tape (head ++ state ++ env) (tail ++ env) (BitVec.ofNat w (count + 1)) 1 .sub middle stored (by
      simp only [List.length_append]
      dsimp [prepareWords] at fits
      nlinarith)
  simp only [List.length_append] at decremented
  have execution := Caliper.Exec.seq copied decremented
  refine ⟨after, _, _, _, execution, ?_, offset.trans zero, ?_⟩
  · simpa [BinOp.eval, BitVec.ofNat_add, BitVec.add_sub_cancel] using result
  · intro buffer; rw [finalCaps]; exact caps buffer

theorem prepare_time_unit_le (entry state env capacity : Nat) :
    (prepare (w := w) entry state env capacity).staticTime .unit ≤ 8 * prepareWords entry state env capacity + 5 := by
  have bound := Assembly.code_time_unit_le (prepareOperands (w := w) entry state env capacity)
  rw [prepareOperands_length] at bound
  change (Assembly.code (prepareOperands entry state env capacity)).staticTime .unit + 5 ≤ _
  omega

theorem prepare_descriptionWords_le (entry state env capacity : Nat) :
    descriptionWords (prepare (w := w) entry state env capacity) ≤ 26 * prepareWords entry state env capacity + 38 := by
  have bound := Assembly.code_descriptionWords_le (prepareOperands (w := w) entry state env capacity)
  rw [prepareOperands_length] at bound
  rw [prepare, descriptionWords_seq, CellArithmetic.descriptionWords_eq]
  omega

end Signatures.Runtime.CaliperBackend.ListFold
