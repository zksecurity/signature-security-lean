import Proofs.Runtime.Caliper.ProximityTermsLayout

/-! Every coordinate tag, copied slot and scalar weight is emitted by actual
word instructions. The constant coordinate is included even at dimension zero. -/
namespace Signatures.Runtime.CaliperBackend.ProximityTerms
open Caliper BoundedSource Assembly
variable {w dimension : Nat} {F K : Type} [One F]
    (layout : Layouts w F K dimension) (oneValid : layout.scalar.valid (1 : F))

def coordinateOperands (i : Fin (dimension + 1)) : List (Operand w) :=
  .literal (BitVec.ofNat w i.val) ::
    (reads 0 (dimension * layout.scalar.representation.encoding.words) layout.label.representation.encoding.words ++
      Fin.cases
        ((layout.scalar.representation.encoding.encode ⟨1, oneValid⟩).map Operand.literal)
        (fun j => reads 0 (j.val * layout.scalar.representation.encoding.words) layout.scalar.representation.encoding.words) i)

def operands : List (Operand w) :=
  .literal (BitVec.ofNat w (dimension + 1)) ::
    (List.ofFn (coordinateOperands layout oneValid)).flatten

theorem coordinate_length (i : Fin (dimension + 1)) :
    (coordinateOperands layout oneValid i).length = layout.term.representation.encoding.words := by
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp only [coordinateOperands, Fin.cases_zero, Fin.cases_succ, List.length_cons,
      List.length_append, List.length_map, reads_length, Encoding.encode_length]
  all_goals rw [Layouts.term_words]; omega

theorem operands_length : (operands layout oneValid).length = layout.output.representation.encoding.words := by
  simp only [operands, List.length_cons, List.length_flatten, List.map_ofFn, Function.comp_def]
  simp_rw [coordinate_length]
  simp only [List.ofFn_const, List.sum_replicate]
  change (dimension + 1) * _ + 1 = 1 + (dimension + 1) * _
  omega

theorem coordinate_sources (i : Fin (dimension + 1)) :
    SourcesBound (coordinateOperands layout oneValid i) 1 := by
  simp only [coordinateOperands, sourcesBound_literal, sourcesBound_append]
  refine ⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩
  refine Fin.cases ?_ (fun _ => sourcesBound_reads _ _ _ _ (by decide)) i
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

theorem operands_sources : SourcesBound (operands layout oneValid) 1 := by
  rw [operands, sourcesBound_literal]
  intro operand member
  obtain ⟨part, partMember, inPart⟩ := List.mem_flatten.mp member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp partMember
  exact coordinate_sources layout oneValid i operand inPart

theorem coordinate_valid (input : layout.input.Value) (before : State w)
    (represented : layout.input.representation.Holds input before) (i : Fin (dimension + 1)) :
    Valid 1 before (coordinateOperands layout oneValid i) := by
  have size := represented_size _ represented
  rw [layout.input_words] at size
  have fits : (before.bufs 0).size < 2 ^ w := by
    rw [represented_size _ represented]
    exact layout.input.representation.fits
  intro operand member
  simp only [coordinateOperands, List.mem_cons, List.mem_append] at member
  rcases member with rfl | member | member
  · trivial
  · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
  · revert member
    refine Fin.cases ?_ (fun j => ?_) i
    · intro member
      obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
      trivial
    · intro member
      exact reads_valid 1 0 _ _ before (by decide) (by have := j.isLt; nlinarith) fits operand member

theorem operands_valid (input : layout.input.Value) (before : State w)
    (represented : layout.input.representation.Holds input before) :
    Valid 1 before (operands layout oneValid) := by
  intro operand member
  rcases List.mem_cons.mp member with rfl | member
  · trivial
  · obtain ⟨part, partMember, inPart⟩ := List.mem_flatten.mp member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp partMember
    exact coordinate_valid layout oneValid input before represented i operand inPart

def termValue (input : layout.input.Value) (i : Fin (dimension + 1)) : layout.term.Value :=
  ⟨((i, input.val.2), Fin.cases 1 input.val.1 i), ⟨trivial, input.property.2⟩,
    Fin.cases oneValid input.property.1 i⟩

theorem coordinate_values (input : layout.input.Value) (before : State w)
    (represented : layout.input.representation.Holds input before) (i : Fin (dimension + 1)) :
    values (coordinateOperands layout oneValid i) before =
      layout.term.representation.encoding.encode (termValue layout oneValid input i) := by
  let vectorBytes := layout.vector.representation.encoding.encode ⟨input.val.1, input.property.1⟩
  let labelBytes := layout.label.representation.encoding.encode ⟨input.val.2, input.property.2⟩
  have contents : (before.bufs 0).toList = vectorBytes ++ labelBytes := represented.2.1
  have labelRead := ListFold.reads_block vectorBytes labelBytes [] before (by simpa using contents)
  dsimp only [vectorBytes, labelBytes] at labelRead
  simp only [Encoding.encode_length, Layouts.vector_words] at labelRead
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [coordinateOperands, Fin.cases_zero, Fin.val_zero, values, List.map_cons,
      List.map_append, List.map_map, Operand.value]
    change _ :: (values (reads 0 _ _) before ++ _) = _
    rw [labelRead]
    rw [show (layout.scalar.representation.encoding.encode (⟨1, oneValid⟩ : layout.scalar.Value)).map
      ((Operand.value before) ∘ Operand.literal) = layout.scalar.representation.encoding.encode ⟨1, oneValid⟩
      from List.map_id _]
    rfl
  · have scalarRead := vectorEncoding_read layout.scalar dimension
      ⟨input.val.1, input.property.1⟩ [] labelBytes before (by exact contents) j
    simp only [List.length_nil, Nat.zero_add] at scalarRead
    simp only [coordinateOperands, Fin.cases_succ, values, List.map_cons, List.map_append, Operand.value]
    change _ :: (values (reads 0 _ _) before ++ values (reads 0 _ _) before) = _
    rw [labelRead, scalarRead]
    rfl

theorem operands_values (input : layout.input.Value) (before : State w)
    (represented : layout.input.representation.Holds input before) :
    values (operands layout oneValid) before =
      layout.output.representation.encoding.encode
        ⟨value input.val, preserves layout oneValid input.val input.property⟩ := by
  have encoded := boundedList_encode_ofFn layout.term (dimension + 1) layout.countFits
    layout.output.representation.fits (termValue layout oneValid input)
  change layout.output.representation.encoding.encode
    ⟨value input.val, preserves layout oneValid input.val input.property⟩ = _ at encoded
  rw [encoded]
  simp only [operands, values, List.map_cons, List.map_flatten, List.map_ofFn, Operand.value]
  congr 2
  apply congrArg List.ofFn
  funext i
  exact coordinate_values layout oneValid input before represented i

end Signatures.Runtime.CaliperBackend.ProximityTerms
