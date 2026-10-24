import Proofs.Runtime.Caliper.ListDestruct

/-! A local Caliper implementation of bounded list case analysis. The resulting
tagged value is the same mathematical empty/head-tail split used by the source
language. The nonempty tail has a capacity one smaller than the input list. -/

namespace Signatures.Runtime.CaliperBackend.ListDestruct

open Caliper

variable {w : Nat} {A : Type}

def split {capacity : Nat} : BoundedList A (capacity + 1) → Unit ⊕ (A × BoundedList A capacity)
  | ⟨[], _⟩ => .inl ()
  | ⟨head :: tail, valid⟩ => .inr (head, ⟨tail, by simpa using valid⟩)

def output (entry : Representation w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w) (storageFits : outputWords entry.encoding.words capacity < 2 ^ w) :
    Representation w (Unit ⊕ (A × BoundedList A capacity)) :=
  (⟨Encoding.unit w, by simp [Encoding.unit, Encoding.checked]⟩ : Representation w Unit).sum
    (entry.prod (entry.boundedList capacity (by omega) (by dsimp [outputWords] at storageFits; nlinarith)) (by
      change entry.encoding.words + (1 + capacity * entry.encoding.words) < 2 ^ w
      dsimp [outputWords] at storageFits
      nlinarith))
    (width_pos hw) (by
      change 1 + max 0 (entry.encoding.words + (1 + capacity * entry.encoding.words)) < 2 ^ w
      rw [Nat.zero_max]
      dsimp [outputWords] at storageFits
      nlinarith)

theorem output_left (entry : Representation w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w) (storageFits : outputWords entry.encoding.words capacity < 2 ^ w) :
    (output entry capacity hw countFits storageFits).encoding.encode (.inl ()) =
      List.replicate (outputWords entry.encoding.words capacity) 0 := by
  change 0 :: ([] ++ List.replicate (max 0 (entry.encoding.words + (1 + capacity * entry.encoding.words)) - 0) 0) = _
  simp only [Nat.zero_max, Nat.sub_zero, List.nil_append]
  have size : outputWords entry.encoding.words capacity =
      (entry.encoding.words + (1 + capacity * entry.encoding.words)) + 1 := by dsimp [outputWords]; ring
  rw [size, List.replicate_succ]

theorem output_right (entry : Representation w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w) (storageFits : outputWords entry.encoding.words capacity < 2 ^ w)
    (head : A) (tail : BoundedList A capacity) :
    (output entry capacity hw countFits storageFits).encoding.encode (.inr (head, tail)) =
      1 :: (entry.encoding.encode head ++ BitVec.ofNat w tail.val.length ::
        (entry.encoding.pack tail.val ++ List.replicate ((capacity - tail.val.length) * entry.encoding.words) 0)) := by
  change 1 :: ((entry.encoding.encode head ++ BitVec.ofNat w tail.val.length ::
    (entry.encoding.pack tail.val ++ List.replicate ((capacity - tail.val.length) * entry.encoding.words) 0)) ++
    List.replicate (max 0 (entry.encoding.words + (1 + capacity * entry.encoding.words)) -
      (entry.encoding.words + (1 + capacity * entry.encoding.words))) 0) = _
  simp

def time (cost : CostModel) (entryWords capacity : Nat) : List A → Nat
  | [] => cost.memLoad + (cost.branch + (emptyCode (w := w) entryWords capacity).staticTime cost)
  | _ :: _ => cost.memLoad + (cost.branch + (nonemptyCode (w := w) entryWords capacity).staticTime cost)

def realizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w) (storageFits : outputWords entry.encoding.words capacity < 2 ^ w) :
    Realizer cost
      (entry.boundedList (capacity + 1) countFits (by dsimp [outputWords] at storageFits; omega))
      (output entry capacity hw countFits storageFits) split where
  code := code entry.encoding.words capacity
  positive_width := width_pos hw
  description_fits := code_descriptionFits _ _ hw storageFits
  random_free := code_randomFree _ _
  time value := time (w := w) cost entry.encoding.words capacity value.val
  net value := time (w := w) cost entry.encoding.words capacity value.val
  workspace value := time (w := w) cost entry.encoding.words capacity value.val
  correct tape value before represented := by
    rcases value with ⟨values, valid⟩
    cases values with
    | nil =>
      have contents : (before.bufs 0).toList = 0 :: List.replicate ((capacity + 1) * entry.encoding.words) 0 := by
        simpa [Representation.boundedList, Encoding.boundedList, Encoding.checked, Encoding.pack] using represented.2.1
      have loaded := Dispatch.load_tag cost tape 0 _ before represented.1 contents
      obtain ⟨after, elapsed, net, peak, called, result, zero, caps⟩ :=
        empty_exec cost tape entry.encoding.words capacity (before.setReg 1 0) storageFits represented.2.2.2
      have exactTime := called.straight_time_eq (Assembly.code_straight _)
      subst elapsed
      have execution := Caliper.Exec.seq loaded (Caliper.Exec.ifNZ_false (c := 1)
        (thn := nonemptyCode entry.encoding.words capacity) (by simp) called)
      refine ⟨after, _, _, execution, ⟨zero.trans represented.1, ?_,
        execution.wellFormed_preserved represented.2.2.1, caps⟩,
        execution.net_le_time allocation, execution.peak_le_time allocation⟩
      rw [split, output_left]
      exact result
    | cons head tail =>
      let payload := entry.encoding.pack tail ++ List.replicate ((capacity - tail.length) * entry.encoding.words) 0
      have tailValid : tail.length ≤ capacity := by simpa using valid
      have payloadSize : payload.length = capacity * (entry.encoding.encode head).length := by
        simp only [payload, List.length_append, Encoding.pack_length, List.length_replicate, entry.encoding.encode_length]
        rw [← Nat.add_mul, Nat.add_sub_of_le tailValid]
      have contents : (before.bufs 0).toList = BitVec.ofNat w (tail.length + 1) :: (entry.encoding.encode head ++ payload) := by
        simpa [Representation.boundedList, Encoding.boundedList, Encoding.checked, Encoding.pack,
          payload, List.append_assoc] using represented.2.1
      have loaded := Dispatch.load_tag cost tape (BitVec.ofNat w (tail.length + 1)) _ before represented.1 contents
      obtain ⟨after, elapsed, net, peak, called, result, zero, caps⟩ :=
        nonempty_exec cost tape (entry.encoding.encode head) payload (BitVec.ofNat w (tail.length + 1)) capacity payloadSize
          (before.setReg 1 (BitVec.ofNat w (tail.length + 1))) contents
          (by simpa [entry.encoding.encode_length] using storageFits) represented.2.2.2
      rw [entry.encoding.encode_length] at called
      have exactTime := called.straight_time_eq (nonemptyCode_straight _ _)
      subst elapsed
      have nonzero : BitVec.ofNat w (tail.length + 1) ≠ 0 := by
        have fits : tail.length + 1 < 2 ^ w := lt_of_le_of_lt (Nat.add_le_add_right tailValid 1) countFits
        intro equal
        have natural := congrArg BitVec.toNat equal
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at natural
      have execution := Caliper.Exec.seq loaded (Caliper.Exec.ifNZ_true (c := 1)
        (els := emptyCode entry.encoding.words capacity) (by simpa using nonzero) called)
      refine ⟨after, _, _, execution, ⟨zero.trans represented.1, ?_,
        execution.wellFormed_preserved represented.2.2.1, caps⟩,
        execution.net_le_time allocation, execution.peak_le_time allocation⟩
      rw [split, output_right]
      simpa [payload, BitVec.ofNat_add, BitVec.add_sub_cancel] using result

theorem time_unit_le (entryWords capacity : Nat) (values : List A) :
    time (w := w) .unit entryWords capacity values ≤ 8 * outputWords entryWords capacity + 7 := by
  have nonempty := Assembly.code_time_unit_le (operands (w := w) entryWords capacity)
  have empty := Assembly.code_time_unit_le (List.replicate (outputWords entryWords capacity) (.literal (0 : Word w)))
  rw [operands_length] at nonempty
  simp only [List.length_replicate] at empty
  cases values with
  | nil =>
    change 1 + (1 + (Assembly.code (List.replicate (outputWords entryWords capacity) (.literal (0 : Word w)))).staticTime .unit) ≤ _
    omega
  | cons head tail =>
    change 1 + (1 + ((Assembly.code (operands (w := w) entryWords capacity)).staticTime .unit + 5)) ≤ _
    omega

theorem code_descriptionWords_le (entryWords capacity : Nat) :
    descriptionWords (code (w := w) entryWords capacity) ≤ 52 * outputWords entryWords capacity + 59 := by
  have nonempty := Assembly.code_descriptionWords_le (operands (w := w) entryWords capacity)
  have empty := Assembly.code_descriptionWords_le (List.replicate (outputWords entryWords capacity) (.literal (0 : Word w)))
  rw [operands_length] at nonempty
  simp only [List.length_replicate] at empty
  have branchWords (yes no : Stmt w) : descriptionWords (.ifNZ 1 yes no) =
      descriptionWords yes + descriptionWords no + 2 := by simp [descriptionWords, description]
  rw [code, descriptionWords_seq, branchWords, nonemptyCode, descriptionWords_seq,
    CellArithmetic.descriptionWords_eq]
  have loadWords : descriptionWords (.memLoad 1 0 0 : Stmt w) = 4 := rfl
  rw [loadWords]
  change 4 + (descriptionWords (Assembly.code (operands entryWords capacity)) + 23 + 1 +
    descriptionWords (Assembly.code (List.replicate (outputWords entryWords capacity) (.literal 0))) + 2) + 1 ≤ _
  omega

end Signatures.Runtime.CaliperBackend.ListDestruct
