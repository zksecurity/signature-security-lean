import Proofs.Runtime.Caliper.ListConstruct

/-! Capacity growth copies and pads the represented list. Increasing a logical
capacity is not a free change of encoding: all reserved output words are built
by the returned Caliper program. -/

namespace Signatures.Runtime.CaliperBackend.ListCapacity

open Caliper Assembly

variable {w : Nat} {A : Type}

def operands (entryWords source target : Nat) : List (Operand w) :=
  reads 0 0 (1 + source * entryWords) ++ List.replicate ((target - source) * entryWords) (.literal 0)

theorem operands_length (entryWords source target : Nat) (increasing : source ≤ target) :
    (operands (w := w) entryWords source target).length = 1 + target * entryWords := by
  simp only [operands, List.length_append, reads_length, List.length_replicate]
  rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_of_le increasing]

def widen {source target : Nat} (increasing : source ≤ target) (value : BoundedList A source) : BoundedList A target :=
  ⟨value.val, value.property.trans increasing⟩

def realizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (entry : Representation w A) (source target : Nat) (increasing : source ≤ target)
    (hw : 16 < 2 ^ w) (countFits : target < 2 ^ w)
    (storageFits : 1 + target * entry.encoding.words < 2 ^ w) :
    Realizer cost (entry.boundedList source (increasing.trans_lt countFits) (by nlinarith))
      (entry.boundedList target countFits storageFits) (widen increasing) :=
  Assembly.realizer cost allocation _ _ _ (operands entry.encoding.words source target) hw
    (operands_length _ _ _ increasing)
    (by
      intro operand member
      simp only [operands, List.mem_append, List.mem_replicate] at member
      rcases member with member | ⟨_, rfl⟩
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · trivial)
    (by
      intro value state represented operand member
      have size := represented_size _ represented
      change (state.bufs 0).size = 1 + source * entry.encoding.words at size
      simp only [operands, List.mem_append, List.mem_replicate] at member
      rcases member with member | ⟨_, rfl⟩
      · exact reads_valid 1 0 0 _ state (by decide) (by omega) (by rw [size]; nlinarith) operand member
      · trivial)
    (by
      intro value state represented
      have size := represented_size _ represented
      change (state.bufs 0).size = 1 + source * entry.encoding.words at size
      have read := reads_values (w := w) 0 0 (1 + source * entry.encoding.words) state (by omega)
      have all : ((state.bufs 0).toList.drop 0).take (1 + source * entry.encoding.words) = (state.bufs 0).toList := by
        simp only [List.drop_zero]
        apply List.take_of_length_le
        simpa using le_of_eq size
      rw [all, represented.2.1] at read
      simp only [operands, values, List.map_append, List.map_replicate, Operand.value]
      rw [show (reads (w := w) 0 0 (1 + source * entry.encoding.words)).map (Operand.value state) =
        (entry.boundedList source (increasing.trans_lt countFits) (by nlinarith)).encoding.encode value from read]
      change (BitVec.ofNat w value.val.length :: (entry.encoding.pack value.val ++
        List.replicate ((source - value.val.length) * entry.encoding.words) 0)) ++
        List.replicate ((target - source) * entry.encoding.words) 0 =
        BitVec.ofNat w value.val.length :: (entry.encoding.pack value.val ++
          List.replicate ((target - value.val.length) * entry.encoding.words) 0)
      have count : (source - value.val.length) + (target - source) = target - value.val.length := by
        have := value.property
        omega
      simp only [List.cons_append, List.append_assoc, ← List.replicate_add, ← Nat.add_mul, count])

theorem time_unit_le (entryWords source target : Nat) (increasing : source ≤ target) :
    (Assembly.code (operands (w := w) entryWords source target)).staticTime .unit ≤ 8 * (1 + target * entryWords) := by
  simpa [operands_length entryWords source target increasing] using Assembly.code_time_unit_le (operands (w := w) entryWords source target)

theorem descriptionWords_le (entryWords source target : Nat) (increasing : source ≤ target) :
    descriptionWords (Assembly.code (operands (w := w) entryWords source target)) ≤ 26 * (1 + target * entryWords) + 14 := by
  simpa [operands_length entryWords source target increasing] using Assembly.code_descriptionWords_le (operands (w := w) entryWords source target)

end Signatures.Runtime.CaliperBackend.ListCapacity
