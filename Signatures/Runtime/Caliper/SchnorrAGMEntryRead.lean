import Signatures.Runtime.Caliper.SchnorrAGMReadBounds

/-! The terminal read keeps the complete cached entry. It reuses the executed
cache lookup and metadata retention; only the final charged output assembly
differs from the challenge-only read used by the query handler. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.EntryRead
open Caliper BoundedSource OracleComp OracleSpec Assembly Read
open Signatures.Runtime.SchnorrAGM.Native
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def output : Layout w (EncodedEntry F × EncodedState F G M) := layout.entry.prod layout.state
  (layout.fits_of_le (by
    change layout.entry.representation.encoding.words +
      (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words) ≤ _
    have := Read.components layout
    omega))

def returnValue (value : Returned layout) : (output layout).Value :=
  ⟨(value.1.1.val.1, value.1.1.val.2, value.2.val.1, value.2.val.2.1, value.2.val.2.2.1, value.1.2.val.2),
    value.1.1.property.1, value.1.1.property.2, value.2.property.1, value.2.property.2.1, trivial, trivial⟩

theorem output_size : (output layout).representation.encoding.words ≤ layout.width := by
  change layout.entry.representation.encoding.words +
    (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words) ≤ _
  have := Read.components layout
  omega

theorem result_bytes (value : Returned layout) : (output layout).representation.encoding.encode (returnValue layout value) =
    layout.entry.representation.encoding.encode (returnedEntry layout value) ++
      layout.cache.lookup.table.representation.encoding.encode (returnedTable layout value) ++
        metadataPrefix layout value.2 ++ [if value.1.2.val.2 then 1 else 0] := by
  change _ ++ (_ ++ (_ ++ (_ ++ ([if value.2.val.2.2.1 then 1 else 0] ++ [if value.1.2.val.2 then 1 else 0])))) = _
  simp only [metadataPrefix, List.append_assoc]
  rfl

def finishOperands : List (Operand w) :=
  reads 0 0 (layout.entry.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words) ++
    reads 0 (layout.entry.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words +
      layout.affine.representation.encoding.words + 1) (prefixWords layout) ++
    reads 0 (layout.entry.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words +
      layout.affine.representation.encoding.words) 1

theorem finishOperands_length : (finishOperands layout).length = (output layout).representation.encoding.words := by
  simp only [finishOperands, List.length_append, reads_length]
  change _ = layout.entry.representation.encoding.words +
    (layout.cache.lookup.table.representation.encoding.words + layout.metadata.representation.encoding.words)
  rw [metadata_words]
  omega

theorem finishOperands_sources : SourcesBound (finishOperands layout) 1 := by
  simp only [finishOperands, sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩

def finish : Realizer .unit (returned layout) (output layout).representation (returnValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (finishOperands layout) layout.wordFits (finishOperands_length layout)
    (by
      intro operand member
      simp only [finishOperands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size =
        ((layout.entry.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words) +
          (layout.affine.representation.encoding.words + 1)) + layout.metadata.representation.encoding.words at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]
        exact (returned layout).fits
      have metaSize := metadata_words layout
      simp only [finishOperands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro value before represented
      have contents := represented.2.1
      rw [returned_bytes] at contents
      let entry := layout.entry.representation.encoding.encode (returnedEntry layout value)
      let table := layout.cache.lookup.table.representation.encoding.encode (returnedTable layout value)
      let affine := layout.affine.representation.encoding.encode (returnedAffine layout value)
      let flag : List (Word w) := [if value.1.2.val.2 then 1 else 0]
      let metadataBytes := layout.metadata.representation.encoding.encode value.2
      change (before.bufs 0).toList = (entry ++ table) ++ (affine ++ flag) ++ metadataBytes at contents
      have entryRead := ListFold.reads_block [] (entry ++ table) ((affine ++ flag) ++ metadataBytes) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have prefixRead := ListFold.reads_block (entry ++ table ++ affine ++ flag)
        (metadataPrefix layout value.2) [if value.2.val.2.2.2 then 1 else 0] before
        (by simpa only [metadataBytes, metadata_bytes, List.append_assoc] using contents)
      have flagRead := ListFold.reads_block (entry ++ table ++ affine) flag metadataBytes before
        (by simpa only [List.append_assoc] using contents)
      dsimp only [entry, table, affine, flag, metadataBytes] at entryRead prefixRead flagRead
      simp only [List.length_nil, List.length_append, Encoding.encode_length, prefix_length,
        List.length_cons, Nat.zero_add] at entryRead prefixRead flagRead
      rw [result_bytes]
      simp only [finishOperands, values, List.map_append]
      change values (reads 0 0 _) before ++ values (reads 0 _ _) before ++ values (reads 0 _ _) before = _
      rw [entryRead, prefixRead, flagRead])

variable {I : Type} [Zero F] [Add F] [DecidableEq F] [DecidableEq M] [DecidableEq G]
    {spec : OracleSpec I} (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)
    (port : Interactive.Port w spec)

def code (sampler : Interactive.Code w) : Interactive.Code w :=
  .seq (.compute (pack layout zeroValid).code)
    (.seq (retained layout zeroValid add addBuffers slotsFit port sampler) (.compute (finish layout).code))

def source (sampler : OracleComp spec layout.scalar.Value) (value : (input layout).Value) :
    OracleComp spec (output layout).Value :=
  (fun result => returnValue layout (result, inputMetadata layout value)) <$>
    Cache.source layout sampler (packValue layout zeroValid value).1

theorem refines {sampler : Interactive.Code w} {sampleSource : OracleComp spec layout.scalar.Value}
    (sampleCorrect : Interactive.Refines port .unit (PairSampling.input w).representation layout.scalar.representation
      (fun _ => sampleSource) sampler) :
    Interactive.Refines port .unit (input layout).representation (output layout).representation
      (source layout zeroValid sampleSource) (code layout zeroValid add addBuffers slotsFit port sampler) := by
  have combined := (Interactive.Refines.compute port .unit (pack layout zeroValid)).seq
    ((retained_refines layout zeroValid add addBuffers slotsFit port sampleCorrect).seq
      (Interactive.Refines.compute port .unit (finish layout)))
  convert combined using 1
  · funext value
    simp only [pure_bind, bind_pure_comp, Functor.map_map, source]
    rfl
  · rfl

end Signatures.Runtime.CaliperBackend.SchnorrAGM.EntryRead
