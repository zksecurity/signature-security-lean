import Signatures.Runtime.Caliper.SchnorrAGMReadBytes

/-! Executed restoration after a cache read. The returned cache and challenge
are combined with the saved metadata prefix and the new mutable bad flag. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def finishOperands : List (Operand w) :=
  reads 0 0 layout.scalar.representation.encoding.words ++
    reads 0 layout.entry.representation.encoding.words layout.cache.lookup.table.representation.encoding.words ++
    reads 0 (layout.entry.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words +
      layout.affine.representation.encoding.words + 1) (prefixWords layout) ++
    reads 0 (layout.entry.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words +
      layout.affine.representation.encoding.words) 1

theorem finishOperands_length : (finishOperands layout).length = (output layout).representation.encoding.words := by
  simp only [finishOperands, List.length_append, reads_length]
  change _ = layout.scalar.representation.encoding.words +
    (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words)
  rw [metadata_words]; omega

theorem finishOperands_sources : SourcesBound (finishOperands layout) 1 := by
  simp only [finishOperands, sourcesBound_append]
  exact ⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩

def finish : Realizer .unit (returned layout) (output layout).representation (returnValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (finishOperands layout) layout.wordFits (finishOperands_length layout)
    (by
      intro operand member
      simp only [finishOperands, List.mem_append] at member
      rcases member with ((member | member) | member) | member <;>
        exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size =
        ((layout.entry.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words) +
          (layout.affine.representation.encoding.words + 1)) + layout.metadata.representation.encoding.words at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact (returned layout).fits
      have metaSize := metadata_words layout
      have entrySize := layout.entry_words
      simp only [finishOperands, List.mem_append] at member
      rcases member with ((member | member) | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro value before represented
      have contents := represented.2.1
      rw [returned_bytes] at contents
      let entry := layout.entry.representation.encoding.encode (returnedEntry layout value)
      let challenge := layout.scalar.representation.encoding.encode (returnedChallenge layout value)
      let entryTail := layout.optionalAffine.representation.encoding.encode ⟨value.1.1.val.1.2, value.1.1.property.1.2⟩
      let table := layout.cache.lookup.table.representation.encoding.encode (returnedTable layout value)
      let affine := layout.affine.representation.encoding.encode (returnedAffine layout value)
      let flag : List (Word w) := [if value.1.2.val.2 then 1 else 0]
      let metadataBytes := layout.metadata.representation.encoding.encode value.2
      change (before.bufs 0).toList = (entry ++ table) ++ (affine ++ flag) ++ metadataBytes at contents
      have entrySplit : entry = challenge ++ entryTail := rfl
      have challengeRead := ListFold.reads_block [] challenge (entryTail ++ table ++ affine ++ flag ++ metadataBytes) before (by
        simpa only [entrySplit, List.nil_append, List.append_assoc] using contents)
      have tableRead := ListFold.reads_block entry table ((affine ++ flag) ++ metadataBytes) before
        (by simpa only [List.append_assoc] using contents)
      have prefixRead := ListFold.reads_block (entry ++ table ++ affine ++ flag)
        (metadataPrefix layout value.2) [if value.2.val.2.2.2 then 1 else 0] before
        (by simpa only [metadataBytes, metadata_bytes, List.append_assoc] using contents)
      have flagRead := ListFold.reads_block (entry ++ table ++ affine) flag metadataBytes before
        (by simpa only [List.append_assoc] using contents)
      dsimp only [entry, challenge, table, affine, flag, metadataBytes] at challengeRead tableRead prefixRead flagRead
      simp only [List.length_nil, List.length_append, Encoding.encode_length, prefix_length,
        List.length_cons, Nat.zero_add] at challengeRead tableRead prefixRead flagRead
      rw [result_bytes]
      simp only [finishOperands, values, List.map_append]
      change values (reads 0 0 _) before ++ values (reads 0 _ _) before ++
        values (reads 0 _ _) before ++ values (reads 0 _ _) before = _
      rw [challengeRead, tableRead, prefixRead, flagRead])

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Read
