import Proofs.Runtime.Caliper.PairBounds

/-! Literal construction of a represented constant. Its entire encoding appears
in stored code and is written by executed instructions. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper Assembly

variable {w : Nat} {A B : Type} (input : Layout w A) (output : Layout w B)
    (value : output.Value) (hw : 16 < 2 ^ w)

def Implementation.constant : Implementation .unit input output (fun _ => value.val) where
  preserves _ _ := value.property
  program := Assembly.realizer .unit (by decide) input.representation output.representation _
    ((output.representation.encoding.encode value).map Operand.literal) hw
    (by simp only [List.length_map, Encoding.encode_length])
    (by intro operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)
    (by intro source state represented operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)
    (by intro source state represented; simp only [Assembly.values, List.map_map]; exact List.map_id _)

theorem Implementation.constant_bounded : (Implementation.constant input output value hw).BoundedBy
    (8 * output.representation.encoding.words) (26 * output.representation.encoding.words + 14) := by
  constructor
  · intro source
    change (Assembly.code ((output.representation.encoding.encode value).map Operand.literal)).staticTime .unit ≤ _
    simpa only [List.length_map, Encoding.encode_length] using
      Assembly.code_time_unit_le ((output.representation.encoding.encode value).map Operand.literal)
  · change descriptionWords (Assembly.code ((output.representation.encoding.encode value).map Operand.literal)) ≤ _
    simpa only [List.length_map, Encoding.encode_length] using
      Assembly.code_descriptionWords_le ((output.representation.encoding.encode value).map Operand.literal)

theorem Implementation.constant_buffers : (Implementation.constant input output value hw).program.code.memBound ≤ 2 :=
  (Assembly.code_names _ 1 (by
    intro operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)).2

theorem Implementation.constant_names (slots : Nat) : NamesAccounted (Implementation.constant input output value hw).program.code slots :=
  Assembly.code_namesAccounted _ slots (by
    intro operand member; obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial)

end Signatures.Runtime.CaliperBackend.BoundedSource
