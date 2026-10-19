import Signatures.Runtime.Caliper.SchnorrAGMFlattenStep

/-! Paid setup for positional attachment and affine summation. Both the
missing-coefficient default and the initial zero accumulator are stored scalar
encodings, copied into the actual runtime frames. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
open Caliper BoundedSource Assembly
variable {w : Nat} {F : Type} [Zero F] (layout : Layouts w F) (zeroValid : layout.scalar.valid 0)

def prepareOperands : List (Operand w) :=
  reads 0 0 layout.attach.keys.representation.encoding.words ++
    (layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩).map Operand.literal ++
    reads 0 layout.attach.keys.representation.encoding.words layout.attach.values.representation.encoding.words

theorem prepareOperands_length : (prepareOperands layout zeroValid).length = layout.attach.input.representation.encoding.words := by
  simp only [prepareOperands, List.length_append, List.length_map, reads_length, Encoding.encode_length]
  change _ = layout.attach.keys.representation.encoding.words +
    (layout.scalar.representation.encoding.words + layout.attach.values.representation.encoding.words)
  omega

theorem prepareOperands_sources : SourcesBound (prepareOperands layout zeroValid) 1 := by
  simp only [prepareOperands, sourcesBound_append]
  refine ⟨⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

def prepare : Implementation .unit layout.input layout.attach.input (fun value => (value.1, 0, value.2)) where
  preserves _ valid := ⟨valid.1, zeroValid, valid.2⟩
  program := Assembly.realizer .unit (by decide) _ _ _ (prepareOperands layout zeroValid) layout.wordFits
    (prepareOperands_length layout zeroValid)
    (by
      intro operand member
      simp only [prepareOperands, List.mem_append] at member
      rcases member with (member | member) | member
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial
      · exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size : (before.bufs 0).size = layout.attach.keys.representation.encoding.words +
          layout.attach.values.representation.encoding.words := represented_size _ represented
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [size]; exact layout.input.representation.fits
      simp only [prepareOperands, List.mem_append] at member
      rcases member with (member | member) | member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro value before represented
      let keys := layout.attach.keys.representation.encoding.encode ⟨value.val.1, value.property.1⟩
      let coefficients := layout.attach.values.representation.encoding.encode ⟨value.val.2, value.property.2⟩
      have contents : (before.bufs 0).toList = keys ++ coefficients := represented.2.1
      have keysRead := ListFold.reads_block [] keys coefficients before (by simpa using contents)
      have coefficientsRead := ListFold.reads_block keys coefficients [] before (by simpa using contents)
      dsimp only [keys, coefficients] at keysRead coefficientsRead
      simp only [List.length_nil, Encoding.encode_length] at keysRead coefficientsRead
      simp only [prepareOperands, values, List.map_append, List.map_map]
      change values (reads 0 0 _) before ++ _ ++ values (reads 0 _ _) before = _
      rw [keysRead, coefficientsRead]
      have literals : (layout.scalar.representation.encoding.encode (⟨0, zeroValid⟩ : layout.scalar.Value)).map
          ((Operand.value before) ∘ Operand.literal) = layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩ := List.map_id _
      rw [literals]
      change (_ ++ _) ++ _ = _ ++ (_ ++ _)
      exact List.append_assoc _ _ _)

def initialOperands : List (Operand w) :=
  reads 0 0 layout.rows.representation.encoding.words ++
    ((layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩) ++
      (layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩)).map Operand.literal

theorem initialOperands_length : (initialOperands layout zeroValid).length = layout.frame.representation.encoding.words := by
  simp only [initialOperands, List.length_append, List.length_map, reads_length, Encoding.encode_length]
  change _ = layout.rows.representation.encoding.words + (layout.affine.representation.encoding.words + 0)
  rw [Layouts.affine_words]; omega

theorem initialOperands_sources : SourcesBound (initialOperands layout zeroValid) 1 := by
  apply (sourcesBound_append _ _ _).mpr
  refine ⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

def initial : Implementation .unit layout.rows layout.frame (fun rows => (rows, (0, 0), ())) where
  preserves _ valid := ⟨valid, ⟨zeroValid, zeroValid⟩, trivial⟩
  program := Assembly.realizer .unit (by decide) _ _ _ (initialOperands layout zeroValid) layout.wordFits
    (initialOperands_length layout zeroValid)
    (by
      intro operand member
      rcases List.mem_append.mp member with copied | literal
      · exact reads_namesFit 0 _ _ (by positivity) operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial)
    (by
      intro value before represented operand member
      rcases List.mem_append.mp member with copied | literal
      · exact reads_valid 1 0 0 _ before (by decide) (by rw [represented_size _ represented]; omega)
          (by rw [represented_size _ represented]; exact layout.rows.representation.fits) operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial)
    (by
      intro value before represented
      have copied := ListFold.reads_block [] (layout.rows.representation.encoding.encode value) [] before
        (by simpa using represented.2.1)
      simp only [List.length_nil, Encoding.encode_length] at copied
      simp only [initialOperands, values, List.map_append, List.map_map]
      change values (reads 0 0 _) before ++ _ = _
      rw [copied]
      have literals : (layout.scalar.representation.encoding.encode (⟨0, zeroValid⟩ : layout.scalar.Value)).map
          ((Operand.value before) ∘ Operand.literal) = layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩ := List.map_id _
      rw [literals]
      change _ ++ (_ ++ _) = _ ++ ((_ ++ _) ++ [])
      simp only [List.append_nil]
      rfl)

theorem prepare_bounded : (prepare layout zeroValid).BoundedBy
    (8 * layout.attach.input.representation.encoding.words) (26 * layout.attach.input.representation.encoding.words + 14) := by
  constructor
  · intro value
    have bound := code_time_unit_le (prepareOperands layout zeroValid)
    rw [prepareOperands_length] at bound
    exact bound
  · have bound := code_descriptionWords_le (prepareOperands layout zeroValid)
    rw [prepareOperands_length] at bound
    exact bound

theorem initial_bounded : (initial layout zeroValid).BoundedBy
    (8 * layout.frame.representation.encoding.words) (26 * layout.frame.representation.encoding.words + 14) := by
  constructor
  · intro value
    have bound := code_time_unit_le (initialOperands layout zeroValid)
    rw [initialOperands_length] at bound
    exact bound
  · have bound := code_descriptionWords_le (initialOperands layout zeroValid)
    rw [initialOperands_length] at bound
    exact bound

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Flatten
