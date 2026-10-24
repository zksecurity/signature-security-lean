import Proofs.Runtime.Caliper.ListFoldSetup

/-! Executed permutation of three encoded blocks. This is used to restore a
fold's list/accumulator/environment frame after its body returns. -/

namespace Signatures.Runtime.CaliperBackend.Reorder

open Caliper Assembly

variable {w : Nat} {A B D : Type}

def operands (first second third : Nat) : List (Operand w) :=
  reads 0 first second ++ reads 0 0 first ++ reads 0 (first + second) third

theorem operands_length (first second third : Nat) :
    (operands (w := w) first second third).length = first + second + third := by
  simp [operands, reads_length]; omega

theorem operands_names (first second third : Nat) :
    ∀ operand ∈ operands (w := w) first second third, operand.NamesFit := by
  intro operand member
  simp only [operands, List.mem_append] at member
  rcases member with (member | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

theorem operands_valid (first second third : Nat) (before : State w)
    (size : (before.bufs 0).size = first + second + third)
    (fits : (before.bufs 0).size < 2 ^ w) : Valid 1 before (operands first second third) := by
  intro operand member
  simp only [operands, List.mem_append] at member
  rcases member with (member | member) | member <;>
    exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member

theorem operands_values (first second third : List (Word w)) (before : State w)
    (contents : (before.bufs 0).toList = first ++ second ++ third) :
    values (operands first.length second.length third.length) before = second ++ first ++ third := by
  have one := ListFold.reads_block first second third before contents
  have two := ListFold.reads_block [] first (second ++ third) before (by simpa [List.append_assoc] using contents)
  have three := ListFold.reads_block (first ++ second) third [] before (by simpa using contents)
  simp only [List.length_nil] at two
  simp only [List.length_append] at three
  simp only [operands, values, List.map_append]
  change values (reads 0 first.length second.length) before ++ values (reads 0 0 first.length) before ++
    values (reads 0 (first.length + second.length) third.length) before = _
  rw [one, two, three]

def realizer (cost : CostModel) (allocation : 1 ≤ cost.allocPerWord)
    (first : Representation w A) (second : Representation w B) (third : Representation w D)
    (hw : 16 < 2 ^ w) (fits : first.encoding.words + second.encoding.words + third.encoding.words < 2 ^ w) :
    Realizer cost
      (first.prod (second.prod third (by omega)) (by change first.encoding.words + (second.encoding.words + third.encoding.words) < 2 ^ w; omega))
      (second.prod (first.prod third (by omega)) (by change second.encoding.words + (first.encoding.words + third.encoding.words) < 2 ^ w; omega))
      (fun value => (value.2.1, (value.1, value.2.2))) :=
  Assembly.realizer cost allocation _ _ _ (operands first.encoding.words second.encoding.words third.encoding.words) hw
    (by rw [operands_length]; change first.encoding.words + second.encoding.words + third.encoding.words = second.encoding.words + (first.encoding.words + third.encoding.words); omega)
    (operands_names _ _ _)
    (by
      intro value state represented
      have size := represented_size _ represented
      change (state.bufs 0).size = first.encoding.words + (second.encoding.words + third.encoding.words) at size
      exact operands_valid _ _ _ state (by omega) (by omega))
    (by
      intro value state represented
      have read := operands_values (first.encoding.encode value.1) (second.encoding.encode value.2.1)
        (third.encoding.encode value.2.2) state (by simpa [Representation.prod, Encoding.prod, Encoding.checked, List.append_assoc] using represented.2.1)
      simpa [first.encoding.encode_length, second.encoding.encode_length, third.encoding.encode_length,
        Representation.prod, Encoding.prod, Encoding.checked, List.append_assoc] using read)

theorem time_unit_le (first second third : Nat) :
    (Assembly.code (operands (w := w) first second third)).staticTime .unit ≤ 8 * (first + second + third) := by
  simpa [operands_length] using Assembly.code_time_unit_le (operands (w := w) first second third)

theorem descriptionWords_le (first second third : Nat) :
    descriptionWords (Assembly.code (operands (w := w) first second third)) ≤ 26 * (first + second + third) + 14 := by
  simpa [operands_length] using Assembly.code_descriptionWords_le (operands (w := w) first second third)

end Signatures.Runtime.CaliperBackend.Reorder
