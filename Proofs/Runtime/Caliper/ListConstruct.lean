import Proofs.Runtime.Caliper.CellArithmetic

/-! Bounded list construction with actual memory instructions. A list stores a
length word, its entries, and charged zero padding up to capacity. Prepending an
entry copies the payload and increments the stored length; no host list operation
is used by execution. The output capacity is explicitly one larger than the
input capacity. -/

namespace Signatures.Runtime.CaliperBackend.ListConstruct

open Caliper Assembly

variable {w : Nat} {A : Type}

/-- Even the empty list allocates and initializes its declared capacity. -/
def emptyRealizer {B : Type} (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (input : Representation w B) (entry : Representation w A) (capacity : Nat)
    (hw : 16 < 2 ^ w) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words < 2 ^ w) :
    Realizer cost input (entry.boundedList capacity countFits storageFits)
      (fun _ => ⟨[], by simp⟩) :=
  Assembly.realizer cost allocation input (entry.boundedList capacity countFits storageFits) _
    (List.replicate (1 + capacity * entry.encoding.words) (.literal 0)) hw (by simp; rfl)
    (by intro operand member; simp only [List.mem_replicate] at member; rcases member with ⟨_, rfl⟩; trivial)
    (by intro value state represented operand member; simp only [List.mem_replicate] at member; rcases member with ⟨_, rfl⟩; trivial)
    (by
      intro value state represented
      simp [values, Operand.value, Representation.boundedList, Encoding.boundedList,
        Encoding.checked, Encoding.pack, Nat.add_comm 1, List.replicate_succ])

def consOperands (entryWords capacity : Nat) : List (Operand w) :=
  reads 0 entryWords 1 ++ reads 0 0 entryWords ++ reads 0 (entryWords + 1) (capacity * entryWords)

theorem consOperands_length (entryWords capacity : Nat) :
    (consOperands (w := w) entryWords capacity).length = 1 + (capacity + 1) * entryWords := by
  simp [consOperands, reads_length]; ring

theorem consOperands_names (entryWords capacity : Nat) :
    ∀ operand ∈ consOperands (w := w) entryWords capacity, operand.NamesFit := by
  intro operand member
  simp only [consOperands, List.mem_append] at member
  rcases member with (member | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

theorem consOperands_valid (entryWords capacity : Nat) (before : State w)
    (size : (before.bufs 0).size = 1 + (capacity + 1) * entryWords)
    (fits : (before.bufs 0).size < 2 ^ w) : Valid 1 before (consOperands entryWords capacity) := by
  intro operand member
  simp only [consOperands, List.mem_append] at member
  rcases member with (member | member) | member <;>
    exact reads_valid 1 0 _ _ before (by decide) (by rw [size]; nlinarith) fits operand member

theorem consOperands_values (head payload : List (Word w)) (length : Word w)
    (capacity : Nat) (payloadSize : payload.length = capacity * head.length)
    (before : State w) (contents : (before.bufs 0).toList = head ++ length :: payload) :
    values (consOperands head.length capacity) before = length :: (head ++ payload) := by
  have size := congrArg List.length contents
  simp only [Array.length_toList, List.length_append, List.length_cons, payloadSize] at size
  have h₁ := reads_values (w := w) 0 head.length 1 before (by omega)
  have h₂ := reads_values (w := w) 0 0 head.length before (by omega)
  have h₃ := reads_values (w := w) 0 (head.length + 1) (capacity * head.length) before (by omega)
  simp only [consOperands, values, List.map_append]
  change values (reads 0 head.length 1) before ++ values (reads 0 0 head.length) before ++
    values (reads 0 (head.length + 1) (capacity * head.length)) before = _
  rw [h₁, h₂, h₃, contents, ← payloadSize]
  simp

def consCode (entryWords capacity : Nat) : Stmt w :=
  Assembly.code (consOperands entryWords capacity) ;; CellArithmetic.code 0 .add 1

theorem consCode_straight (entryWords capacity : Nat) : (consCode (w := w) entryWords capacity).Straight :=
  ⟨code_straight _, CellArithmetic.straight _ _ _⟩

theorem consCode_randomFree (entryWords capacity : Nat) : (consCode (w := w) entryWords capacity).RandomFree :=
  ⟨code_randomFree _, CellArithmetic.randomFree _ _ _⟩

theorem consCode_descriptionFits (entryWords capacity : Nat) (hw : 16 < 2 ^ w)
    (fits : 1 + (capacity + 1) * entryWords < 2 ^ w) :
    DescriptionFits (consCode (w := w) entryWords capacity) :=
  DescriptionFits.seq (width_pos hw)
    (code_descriptionFits _ hw (by rw [consOperands_length]; exact fits) (consOperands_names _ _))
    (CellArithmetic.descriptionFits _ _ _ hw)

theorem consCode_time_unit_le (entryWords capacity : Nat) :
    (consCode (w := w) entryWords capacity).staticTime .unit ≤
      8 * (1 + (capacity + 1) * entryWords) + 5 := by
  have bound := code_time_unit_le (consOperands (w := w) entryWords capacity)
  rw [consOperands_length] at bound
  simpa [consCode, CellArithmetic.code, Stmt.staticTime, CostModel.unit] using Nat.add_le_add_right bound 5

theorem consCode_descriptionWords_le (entryWords capacity : Nat) :
    descriptionWords (consCode (w := w) entryWords capacity) ≤
      26 * (1 + (capacity + 1) * entryWords) + 38 := by
  have bound := code_descriptionWords_le (consOperands (w := w) entryWords capacity)
  rw [consOperands_length] at bound
  rw [consCode, descriptionWords_seq, CellArithmetic.descriptionWords_eq]
  omega

theorem consCode_exec (cost : CostModel) (tape : RandomTape w)
    (head payload : List (Word w)) (length : Word w) (capacity : Nat)
    (payloadSize : payload.length = capacity * head.length)
    (before : State w) (contents : (before.bufs 0).toList = head ++ length :: payload)
    (fits : 1 + (capacity + 1) * head.length < 2 ^ w)
    (capacities : ∀ buffer, before.caps buffer < 2 ^ w) :
    ∃ after elapsed net peak,
      Caliper.Exec cost tape (consCode head.length capacity) before after elapsed net peak ∧
      (after.bufs 0).toList = (length + 1) :: (head ++ payload) ∧
      after.regs 0 = before.regs 0 ∧ (∀ buffer, after.caps buffer < 2 ^ w) := by
  have size : (before.bufs 0).size = 1 + (capacity + 1) * head.length := by
    have size := congrArg List.length contents
    simp only [Array.length_toList, List.length_append, List.length_cons, payloadSize] at size
    nlinarith
  obtain ⟨middle, time, net, peak, copied, stored, zero, caps⟩ := code_exec cost tape (consOperands head.length capacity)
    before (consOperands_valid _ _ before size (by rw [size]; exact fits))
    (by rw [consOperands_length]; exact fits) capacities
  rw [consOperands_values head payload length capacity payloadSize before contents] at stored
  obtain ⟨after, incremented, result, offset, finalCaps⟩ :=
    CellArithmetic.exec_at cost tape [] (head ++ payload) length 1 .add middle stored (by simp)
  exact ⟨after, _, _, _, Caliper.Exec.seq copied incremented, result, offset.trans zero,
    by intro buffer; rw [finalCaps]; exact caps buffer⟩

def cons {capacity : Nat} (value : A × BoundedList A capacity) : BoundedList A (capacity + 1) :=
  ⟨value.1 :: value.2.val, by simp only [List.length_cons]; exact Nat.add_le_add_right value.2.property 1⟩

def realizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.encoding.words < 2 ^ w) :
    Realizer cost
      (entry.prod (entry.boundedList capacity (by omega) (by nlinarith)) (by
        change entry.encoding.words + (1 + capacity * entry.encoding.words) < 2 ^ w
        nlinarith))
      (entry.boundedList (capacity + 1) countFits storageFits) cons where
  code := consCode entry.encoding.words capacity
  positive_width := width_pos hw
  description_fits := consCode_descriptionFits _ _ hw storageFits
  random_free := consCode_randomFree _ _
  time _ := (consCode (w := w) entry.encoding.words capacity).staticTime cost
  net _ := (consCode (w := w) entry.encoding.words capacity).staticTime cost
  workspace _ := (consCode (w := w) entry.encoding.words capacity).staticTime cost
  correct tape value before represented := by
    let payload := entry.encoding.pack value.2.val ++
      List.replicate ((capacity - value.2.val.length) * entry.encoding.words) 0
    have payloadSize : payload.length = capacity * (entry.encoding.encode value.1).length := by
      simp only [payload, List.length_append, Encoding.pack_length, List.length_replicate, entry.encoding.encode_length]
      rw [← Nat.add_mul, Nat.add_sub_of_le value.2.property]
    obtain ⟨after, elapsed, net, peak, execution, result, zero, caps⟩ := consCode_exec cost tape
      (entry.encoding.encode value.1) payload (BitVec.ofNat w value.2.val.length) capacity payloadSize before represented.2.1
      (by simpa [entry.encoding.encode_length] using storageFits) represented.2.2.2
    rw [entry.encoding.encode_length] at execution
    have ht := execution.straight_time_eq (consCode_straight _ _)
    subst elapsed
    refine ⟨after, net, peak, execution, ⟨zero.trans represented.1, ?_,
      execution.wellFormed_preserved represented.2.2.1, caps⟩,
      execution.net_le_time allocation, execution.peak_le_time allocation⟩
    simpa [cons, Representation.boundedList, Encoding.boundedList, Encoding.checked,
      Encoding.pack, payload, BitVec.ofNat_add, List.append_assoc] using result

end Signatures.Runtime.CaliperBackend.ListConstruct
