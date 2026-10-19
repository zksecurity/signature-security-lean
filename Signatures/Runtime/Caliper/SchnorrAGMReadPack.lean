import Signatures.Runtime.Caliper.SchnorrAGMReadBytes

/-! Executed read setup. The zero fallback is stored code; the key, affine
coefficients, cache and metadata are copied from the current input buffer. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} [Zero F] [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)

def packOperands : List (Operand w) :=
  reads 0 0 layout.key.representation.encoding.words ++
    (layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩ ++ [0]).map Operand.literal ++
    reads 0 layout.key.representation.encoding.words
      (layout.affine.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words) ++
    reads 0 layout.key.representation.encoding.words layout.affine.representation.encoding.words ++
    reads 0 (layout.key.representation.encoding.words + layout.affine.representation.encoding.words +
      layout.cache.lookup.table.representation.encoding.words + prefixWords layout) 1 ++
    reads 0 (layout.key.representation.encoding.words + layout.affine.representation.encoding.words +
      layout.cache.lookup.table.representation.encoding.words) layout.metadata.representation.encoding.words

theorem packOperands_length : (packOperands layout zeroValid).length = (packed layout).encoding.words := by
  simp only [packOperands, List.length_append, List.length_map, Encoding.encode_length, List.length_cons,
    List.length_nil, reads_length]
  change _ = ((layout.key.representation.encoding.words + (layout.scalar.representation.encoding.words +
    (1 + layout.affine.representation.encoding.words) + (layout.cache.lookup.table.representation.encoding.words + 0))) +
    (layout.affine.representation.encoding.words + 1)) + layout.metadata.representation.encoding.words
  omega

omit [DecidableEq M] [DecidableEq G] in
theorem packOperands_sources : SourcesBound (packOperands layout zeroValid) 1 := by
  simp only [packOperands, sourcesBound_append]
  refine ⟨⟨⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
      sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

def pack : Realizer .unit (input layout).representation (packed layout) (packValue layout zeroValid) :=
  Assembly.realizer .unit (by decide) _ _ _ (packOperands layout zeroValid) layout.wordFits
    (packOperands_length layout zeroValid)
    (by
      intro operand member
      simp only [packOperands, List.mem_append] at member
      rcases member with ((((member | member) | member) | member) | member) | member
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = layout.key.representation.encoding.words +
        (layout.affine.representation.encoding.words +
          (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words)) at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact (input layout).representation.fits
      have metaSize := metadata_words layout
      simp only [packOperands, List.mem_append] at member
      rcases member with ((((member | member) | member) | member) | member) | member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp member; trivial
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro value before represented
      have contents := represented.2.1
      rw [input_bytes] at contents
      let key := layout.key.representation.encoding.encode (inputKey layout value)
      let affine := layout.affine.representation.encoding.encode (inputAffine layout value)
      let table := layout.cache.lookup.table.representation.encoding.encode (inputTable layout value)
      let metadataBytes := layout.metadata.representation.encoding.encode (inputMetadata layout value)
      have keyRead := ListFold.reads_block [] key (affine ++ (table ++ metadataBytes)) before (by simpa using contents)
      have bodyRead := ListFold.reads_block key (affine ++ table) metadataBytes before (by simpa only [List.append_assoc] using contents)
      have affineRead := ListFold.reads_block key affine (table ++ metadataBytes) before (by simpa only [List.append_assoc] using contents)
      have flagRead := ListFold.reads_block (key ++ affine ++ table ++ metadataPrefix layout (inputMetadata layout value))
        [if value.val.2.2.2.2.2.2 then 1 else 0] [] before (by
          simpa only [key, affine, table, metadata_bytes, inputMetadata, List.append_assoc, List.append_nil] using contents)
      have metaRead := ListFold.reads_block (key ++ affine ++ table) metadataBytes [] before
        (by simpa only [List.append_nil, List.append_assoc] using contents)
      dsimp only [key, affine, table, metadataBytes] at keyRead bodyRead affineRead flagRead metaRead
      simp only [List.length_nil, List.length_append, Encoding.encode_length, prefix_length,
        List.length_cons] at keyRead bodyRead affineRead flagRead metaRead
      rw [packed_bytes]
      simp only [packOperands, values, List.map_append, List.map_map]
      change values (reads 0 0 _) before ++ _ ++ values (reads 0 _ _) before ++
        values (reads 0 _ _) before ++ values (reads 0 _ _) before ++ values (reads 0 _ _) before = _
      rw [keyRead, bodyRead, affineRead, flagRead, metaRead]
      have literals : (layout.scalar.representation.encoding.encode (⟨0, zeroValid⟩ : layout.scalar.Value) ++ [0]).map
          ((Operand.value before) ∘ Operand.literal) = layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩ ++ [0] :=
        List.map_id _
      simp only [List.map_append] at literals
      rw [literals]
      simp only [List.append_assoc])

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
