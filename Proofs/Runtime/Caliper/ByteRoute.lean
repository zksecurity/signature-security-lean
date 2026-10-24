import Proofs.Runtime.Caliper.StructuralNames

/-! Routing fixed-width frames by executed slices and stored literals.
The byte equation specifies the route; every copied or literal word is emitted
by the existing assembly code, with its time and stored code charged. -/
namespace Signatures.Runtime.CaliperBackend.ByteRoute
open Caliper Assembly

inductive Part (w : Nat) where
  | slice (offset count : Nat)
  | literal (words : List (Word w))

variable {w : Nat}
def operands : List (Part w) → List (Operand w)
  | [] => []
  | .slice offset count :: rest => reads 0 offset count ++ operands rest
  | .literal words :: rest => words.map Operand.literal ++ operands rest
def bytes (input : List (Word w)) : List (Part w) → List (Word w)
  | [] => []
  | .slice offset count :: rest => (input.drop offset).take count ++ bytes input rest
  | .literal words :: rest => words ++ bytes input rest
def words : List (Part w) → Nat
  | [] => 0
  | .slice _ count :: rest => count + words rest
  | .literal value :: rest => value.length + words rest
def Valid (inputWords : Nat) : List (Part w) → Prop
  | [] => True
  | .slice offset count :: rest => offset + count ≤ inputWords ∧ Valid inputWords rest
  | .literal _ :: rest => Valid inputWords rest

theorem length (parts : List (Part w)) : (operands parts).length = words parts := by
  induction parts with
  | nil => rfl
  | cons part parts ih => cases part <;> simp only [operands, words, List.length_append, List.length_map, reads_length, ih]

theorem sources (parts : List (Part w)) : SourcesBound (operands parts) 1 := by
  induction parts with
  | nil => exact sourcesBound_nil _
  | cons part parts ih =>
    cases part with
    | slice offset count => exact (sourcesBound_append _ _ _).mpr ⟨sourcesBound_reads _ _ _ _ (by decide), ih⟩
    | literal value =>
      apply (sourcesBound_append _ _ _).mpr
      refine ⟨?_, ih⟩
      intro operand member
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
      trivial

theorem namesFit (parts : List (Part w)) : ∀ operand ∈ operands parts, operand.NamesFit := by
  intro operand member
  have bound := sources parts operand member
  cases operand with
  | literal word => trivial
  | read source offset =>
    change source < 2 ^ w
    change source + 1 ≤ 1 at bound
    exact (Nat.lt_of_succ_le bound).trans_le Nat.one_le_two_pow

theorem valid (parts : List (Part w)) (state : State w)
    (bounded : Valid (state.bufs 0).size parts) (fits : (state.bufs 0).size < 2 ^ w) :
    Assembly.Valid 1 state (operands parts) := by
  induction parts with
  | nil => simp [Assembly.Valid, operands]
  | cons part parts ih =>
    intro operand member
    cases part with
    | slice offset count =>
      rcases List.mem_append.mp member with member | member
      · exact reads_valid 1 0 offset count state (by decide) bounded.1 fits operand member
      · exact ih bounded.2 operand member
    | literal value =>
      rcases List.mem_append.mp member with member | member
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
        trivial
      · exact ih bounded operand member

theorem values (parts : List (Part w)) (state : State w) (bounded : Valid (state.bufs 0).size parts) :
    Assembly.values (operands parts) state = bytes (state.bufs 0).toList parts := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
    cases part with
    | slice offset count =>
      simp only [operands, Assembly.values, List.map_append, bytes]
      rw [show (reads 0 offset count).map (Operand.value state) =
        ((state.bufs 0).toList.drop offset).take count from reads_values _ _ _ _ bounded.1,
        show (operands parts).map (Operand.value state) = _ from ih bounded.2]
    | literal value =>
      simp only [operands, Assembly.values, List.map_append, List.map_map, bytes, Function.comp_def, Operand.value]
      change value.map id ++ (operands parts).map (Operand.value state) = value ++ bytes (state.bufs 0).toList parts
      rw [List.map_id, show (operands parts).map (Operand.value state) = _ from ih bounded]

theorem slice_block (before block after : List (Word w)) :
    ((before ++ block ++ after).drop before.length).take block.length = block := by
  simp only [List.append_assoc, List.drop_left, List.take_left]

variable {A B : Type} (input : Representation w A) (output : Representation w B)
    (f : A → B) (parts : List (Part w)) (hw : 16 < 2 ^ w)
    (bounded : Valid input.encoding.words parts)
    (size : words parts = output.encoding.words)
    (correct : ∀ value, bytes (input.encoding.encode value) parts = output.encoding.encode (f value))

def realizer : Realizer .unit input output f :=
  Assembly.realizer .unit (by decide) input output f (operands parts) hw
    ((length parts).trans size) (namesFit parts)
    (by
      intro value state represented
      apply valid parts state
      · rwa [represented_size input represented]
      · rw [represented_size input represented]; exact input.fits)
    (by
      intro value state represented
      rw [values parts state (by rwa [represented_size input represented]), represented.2.1]
      exact correct value)

theorem time (value : A) : (realizer input output f parts hw bounded size correct).time value ≤
    8 * output.encoding.words := by
  change (code (operands parts)).staticTime .unit ≤ _
  simpa only [length, size] using code_time_unit_le (operands parts)
theorem codeWords : descriptionWords (realizer input output f parts hw bounded size correct).code ≤
    26 * output.encoding.words + 14 := by
  change descriptionWords (code (operands parts)) ≤ _
  simpa only [length, size] using code_descriptionWords_le (operands parts)
theorem buffers : (realizer input output f parts hw bounded size correct).code.memBound ≤ 2 :=
  (code_names _ 1 (sources parts)).2
theorem names (slots : Nat) : NamesAccounted (realizer input output f parts hw bounded size correct).code slots :=
  code_namesAccounted _ slots (sources parts)

end Signatures.Runtime.CaliperBackend.ByteRoute
