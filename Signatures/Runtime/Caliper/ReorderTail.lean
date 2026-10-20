import Signatures.Runtime.Caliper.Reorder
import Signatures.Runtime.Caliper.NameBounds

/-! Swap the final two encoded blocks with actual copying. This moves a saved
private store after a reply's retained request without changing either value. -/
namespace Signatures.Runtime.CaliperBackend.ReorderTail
open Caliper Assembly
variable {w : Nat} {A B C : Type}

def operands (first second third : Nat) : List (Operand w) :=
  reads 0 0 first ++ reads 0 (first + second) third ++ reads 0 first second
theorem length (first second third : Nat) :
    (operands (w := w) first second third).length = first + third + second := by
  simp only [operands, List.length_append, reads_length]
theorem sources (first second third : Nat) : SourcesBound (operands (w := w) first second third) 1 := by
  simp only [operands, sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩

def realizer (first : Representation w A) (second : Representation w B) (third : Representation w C)
    (hw : 16 < 2 ^ w) (fits : first.encoding.words + second.encoding.words + third.encoding.words < 2 ^ w) :
    Realizer .unit ((first.prod second (by omega)).prod third fits)
      ((first.prod third (by omega)).prod second (by change _ + _ + _ < _; omega))
      (fun value => ((value.1.1, value.2), value.1.2)) :=
  Assembly.realizer .unit (by decide) _ _ _ (operands first.encoding.words second.encoding.words third.encoding.words) hw
    (length _ _ _)
    (by
      intro operand member
      simp only [operands, List.mem_append] at member
      rcases member with (member | member) | member <;> exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = first.encoding.words + second.encoding.words + third.encoding.words at size
      simp only [operands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) (by omega) operand member)
    (by
      intro value before represented
      have contents : (before.bufs 0).toList = first.encoding.encode value.1.1 ++
          second.encoding.encode value.1.2 ++ third.encoding.encode value.2 := represented.2.1
      have one := ListFold.reads_block [] (first.encoding.encode value.1.1)
        (second.encoding.encode value.1.2 ++ third.encoding.encode value.2) before (by simpa [List.append_assoc] using contents)
      have two := ListFold.reads_block (first.encoding.encode value.1.1) (second.encoding.encode value.1.2)
        (third.encoding.encode value.2) before contents
      have three := ListFold.reads_block (first.encoding.encode value.1.1 ++ second.encoding.encode value.1.2)
        (third.encoding.encode value.2) [] before (by simpa using contents)
      simp only [List.length_nil, List.length_append, first.encoding.encode_length,
        second.encoding.encode_length, third.encoding.encode_length] at one two three
      change values (operands _ _ _) before = (first.encoding.encode value.1.1 ++ third.encoding.encode value.2) ++
        second.encoding.encode value.1.2
      simp only [operands, values, List.map_append] at one two three ⊢
      rw [one, three, two])

theorem time (first : Representation w A) (second : Representation w B) (third : Representation w C)
    (hw : 16 < 2 ^ w) (fits : first.encoding.words + second.encoding.words + third.encoding.words < 2 ^ w)
    (value : (A × B) × C) : (realizer first second third hw fits).time value ≤
      8 * (first.encoding.words + second.encoding.words + third.encoding.words) := by
  have bound := code_time_unit_le (operands (w := w) first.encoding.words second.encoding.words third.encoding.words)
  rw [length] at bound
  exact bound.trans (by omega)
theorem words (first : Representation w A) (second : Representation w B) (third : Representation w C)
    (hw : 16 < 2 ^ w) (fits : first.encoding.words + second.encoding.words + third.encoding.words < 2 ^ w) :
    descriptionWords (realizer first second third hw fits).code ≤
      26 * (first.encoding.words + second.encoding.words + third.encoding.words) + 14 := by
  have bound := code_descriptionWords_le (operands (w := w) first.encoding.words second.encoding.words third.encoding.words)
  rw [length] at bound
  exact bound.trans (by omega)
theorem names (first : Representation w A) (second : Representation w B) (third : Representation w C)
    (hw : 16 < 2 ^ w) (fits : first.encoding.words + second.encoding.words + third.encoding.words < 2 ^ w) :
    NamesAccounted (realizer first second third hw fits).code 3 := code_namesAccounted _ _ (sources _ _ _)

end Signatures.Runtime.CaliperBackend.ReorderTail
