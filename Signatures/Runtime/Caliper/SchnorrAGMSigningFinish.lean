import Signatures.Runtime.Caliper.SchnorrAGMSigningComputedBounds

/-! Copy the computed commitment and coefficient together with the saved
sampled request. Cache entries and histories are retained verbatim here; the
following signing stages perform their updates. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def inputMessage (value : layout.input.Value) : layout.scheme.message.Value :=
  ⟨value.val.2.2.2.1, value.property.2.2.2.1⟩
def inputTable (value : layout.input.Value) : layout.scheme.cache.lookup.table.Value :=
  ⟨value.val.2.2.2.2.1, value.property.2.2.2.2.1⟩
def inputMetadata (value : layout.input.Value) : layout.scheme.metadata.Value :=
  ⟨value.val.2.2.2.2.2, value.property.2.2.2.2.2⟩
def commitment (value : layout.computed.Value) : layout.scheme.point.Value := ⟨value.val.1, value.property.1⟩
def coefficient (value : layout.computed.Value) : layout.scheme.scalar.Value := ⟨value.val.2, value.property.2⟩

theorem frame_bytes (value : layout.computed.Value × layout.input.Value) : layout.frame.encoding.encode value =
    (layout.scheme.point.representation.encoding.encode (commitment layout value.1) ++
      layout.scheme.scalar.representation.encoding.encode (coefficient layout value.1)) ++
      ((layout.scheme.scalar.representation.encoding.encode (challenge layout value.2) ++
        layout.scheme.scalar.representation.encoding.encode (response layout value.2)) ++
        (layout.scheme.point.representation.encoding.encode (generator layout value.2) ++
          (layout.scheme.point.representation.encoding.encode (publicKey layout value.2) ++
            (layout.scheme.message.representation.encoding.encode (inputMessage layout value.2) ++
              (layout.scheme.cache.lookup.table.representation.encoding.encode (inputTable layout value.2) ++
                layout.scheme.metadata.representation.encoding.encode (inputMetadata layout value.2)))))) := rfl

variable [Zero F] (zeroValid : layout.scheme.scalar.valid 0)

def finishValue (value : layout.computed.Value × layout.input.Value) : layout.work.Value :=
  ⟨(((value.2.val.2.2.2.1, value.1.val.1), (value.2.val.1.1, false, 0, 0), value.2.val.2.2.2.2.1, ()),
    (value.1.val.1, value.2.val.1.2), (value.2.val.1.2, value.1.val.2), value.2.val.2.2.2.1, value.2.val.2.2.2.2.2),
    ⟨⟨value.2.property.2.2.2.1, value.1.property.1⟩, ⟨value.2.property.1.1, trivial, zeroValid, zeroValid⟩,
      value.2.property.2.2.2.2.1, trivial⟩,
    ⟨value.1.property.1, value.2.property.1.2⟩, ⟨value.2.property.1.2, value.1.property.2⟩,
    value.2.property.2.2.2.1, value.2.property.2.2.2.2.2⟩

def messageOffset : Nat := 3 * layout.scheme.point.representation.encoding.words + 3 * layout.scheme.scalar.representation.encoding.words
def tableOffset : Nat := messageOffset layout + layout.scheme.message.representation.encoding.words
def metadataOffset : Nat := tableOffset layout + layout.scheme.cache.lookup.table.representation.encoding.words

def finishOperands : List (Operand w) :=
  reads 0 (messageOffset layout) layout.scheme.message.representation.encoding.words ++
    reads 0 0 layout.scheme.point.representation.encoding.words ++
    reads 0 (layout.scheme.point.representation.encoding.words + layout.scheme.scalar.representation.encoding.words)
      layout.scheme.scalar.representation.encoding.words ++
    (0 :: (layout.scheme.scalar.representation.encoding.encode ⟨0, zeroValid⟩ ++
      layout.scheme.scalar.representation.encoding.encode ⟨0, zeroValid⟩)).map Operand.literal ++
    reads 0 (tableOffset layout) layout.scheme.cache.lookup.table.representation.encoding.words ++
    reads 0 0 layout.scheme.point.representation.encoding.words ++
    reads 0 (layout.scheme.point.representation.encoding.words + 2 * layout.scheme.scalar.representation.encoding.words)
      layout.scheme.scalar.representation.encoding.words ++
    reads 0 (layout.scheme.point.representation.encoding.words + 2 * layout.scheme.scalar.representation.encoding.words)
      layout.scheme.scalar.representation.encoding.words ++
    reads 0 layout.scheme.point.representation.encoding.words layout.scheme.scalar.representation.encoding.words ++
    reads 0 (messageOffset layout) layout.scheme.message.representation.encoding.words ++
    reads 0 (metadataOffset layout) layout.scheme.metadata.representation.encoding.words

theorem finishOperands_length : (finishOperands layout zeroValid).length = layout.work.representation.encoding.words := by
  simp only [finishOperands, List.length_append, reads_length, List.length_map, List.length_cons, Encoding.encode_length]
  change _ = (layout.scheme.cache.lookup.input.representation.encoding.words +
    ((layout.scheme.point.representation.encoding.words + layout.scheme.scalar.representation.encoding.words) +
      ((layout.scheme.scalar.representation.encoding.words + layout.scheme.scalar.representation.encoding.words) +
        (layout.scheme.message.representation.encoding.words + layout.scheme.metadata.representation.encoding.words))))
  rw [LookupLayout.input_words, layout.cache_width]
  change _ = ((layout.scheme.message.representation.encoding.words + layout.scheme.point.representation.encoding.words) +
    (layout.scheme.scalar.representation.encoding.words + (1 + (layout.scheme.scalar.representation.encoding.words +
      layout.scheme.scalar.representation.encoding.words))) + layout.scheme.cache.lookup.table.representation.encoding.words) + _
  omega

theorem finishOperands_sources : SourcesBound (finishOperands layout zeroValid) 1 := by
  simp only [finishOperands, sourcesBound_append]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, ?_⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

def finish : Realizer .unit layout.frame layout.work.representation (finishValue layout zeroValid) :=
  Assembly.realizer .unit (by decide) _ _ _ (finishOperands layout zeroValid) layout.scheme.wordFits
    (finishOperands_length layout zeroValid)
    (by
      intro operand member
      simp only [finishOperands, List.mem_append] at member
      rcases member with (((((((((copied | copied) | copied) | literal) | copied) | copied) | copied) | copied) | copied) | copied) | copied
      all_goals first
        | exact reads_namesFit 0 _ _ (by positivity) operand copied
        | obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = (layout.scheme.point.representation.encoding.words + layout.scheme.scalar.representation.encoding.words) +
        ((layout.scheme.scalar.representation.encoding.words + layout.scheme.scalar.representation.encoding.words) +
          (layout.scheme.point.representation.encoding.words + (layout.scheme.point.representation.encoding.words +
            (layout.scheme.message.representation.encoding.words + (layout.scheme.cache.lookup.table.representation.encoding.words +
              layout.scheme.metadata.representation.encoding.words))))) at size
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact layout.frame.fits
      simp only [finishOperands, List.mem_append] at member
      rcases member with (((((((((copied | copied) | copied) | literal) | copied) | copied) | copied) | copied) | copied) | copied) | copied
      all_goals try (obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial)
      all_goals
        refine reads_valid 1 0 _ _ before (by decide) ?_ fits operand copied
        try simp only [metadataOffset, tableOffset, messageOffset]
        omega)
    (by
      intro value before represented
      let r := layout.scheme.point.representation.encoding.encode (commitment layout value.1)
      let n := layout.scheme.scalar.representation.encoding.encode (coefficient layout value.1)
      let c := layout.scheme.scalar.representation.encoding.encode (challenge layout value.2)
      let z := layout.scheme.scalar.representation.encoding.encode (response layout value.2)
      let g := layout.scheme.point.representation.encoding.encode (generator layout value.2)
      let pk := layout.scheme.point.representation.encoding.encode (publicKey layout value.2)
      let m := layout.scheme.message.representation.encoding.encode (inputMessage layout value.2)
      let t := layout.scheme.cache.lookup.table.representation.encoding.encode (inputTable layout value.2)
      let metadataBytes := layout.scheme.metadata.representation.encoding.encode (inputMetadata layout value.2)
      have contents : (before.bufs 0).toList = r ++ n ++ c ++ z ++ g ++ pk ++ m ++ t ++ metadataBytes := by
        have contents := represented.2.1
        rw [frame_bytes] at contents
        simpa only [List.append_assoc] using contents
      have hr := ListFold.reads_block [] r (n ++ c ++ z ++ g ++ pk ++ m ++ t ++ metadataBytes) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have hn := ListFold.reads_block r n (c ++ z ++ g ++ pk ++ m ++ t ++ metadataBytes) before
        (by simpa only [List.append_assoc] using contents)
      have hc := ListFold.reads_block (r ++ n) c (z ++ g ++ pk ++ m ++ t ++ metadataBytes) before
        (by simpa only [List.append_assoc] using contents)
      have hz := ListFold.reads_block (r ++ n ++ c) z (g ++ pk ++ m ++ t ++ metadataBytes) before
        (by simpa only [List.append_assoc] using contents)
      have hm := ListFold.reads_block (r ++ n ++ c ++ z ++ g ++ pk) m (t ++ metadataBytes) before
        (by simpa only [List.append_assoc] using contents)
      have ht := ListFold.reads_block (r ++ n ++ c ++ z ++ g ++ pk ++ m) t metadataBytes before
        (by simpa only [List.append_assoc] using contents)
      have hmeta := ListFold.reads_block (r ++ n ++ c ++ z ++ g ++ pk ++ m ++ t) metadataBytes [] before
        (by simpa only [List.append_nil, List.append_assoc] using contents)
      dsimp only [r, n, c, z, g, pk, m, t, metadataBytes] at hr hn hc hz hm ht hmeta
      simp only [List.length_nil, List.length_append, Encoding.encode_length] at hr hn hc hz hm ht hmeta
      have zOffset : layout.scheme.point.representation.encoding.words + layout.scheme.scalar.representation.encoding.words +
          layout.scheme.scalar.representation.encoding.words = layout.scheme.point.representation.encoding.words +
            2 * layout.scheme.scalar.representation.encoding.words := by omega
      have mOffset : layout.scheme.point.representation.encoding.words + layout.scheme.scalar.representation.encoding.words +
          layout.scheme.scalar.representation.encoding.words + layout.scheme.scalar.representation.encoding.words +
            layout.scheme.point.representation.encoding.words + layout.scheme.point.representation.encoding.words = messageOffset layout := by
        unfold messageOffset; omega
      rw [zOffset] at hz
      rw [mOffset] at hm ht hmeta
      simp only [finishOperands, values, List.map_append, List.map_map]
      change values (reads 0 _ _) before ++ values (reads 0 0 _) before ++ values (reads 0 _ _) before ++ _ ++
        values (reads 0 _ _) before ++ values (reads 0 0 _) before ++ values (reads 0 _ _) before ++
        values (reads 0 _ _) before ++ values (reads 0 _ _) before ++ values (reads 0 _ _) before ++ values (reads 0 _ _) before = _
      simp only [metadataOffset, tableOffset]
      rw [hm, hr, hc, ht, hz, hn, hmeta]
      rw [show Operand.value before ∘ Operand.literal = id from rfl, List.map_id]
      change _ = (m ++ r) ++ ((c ++ ([0] ++ (layout.scheme.scalar.representation.encoding.encode ⟨0, zeroValid⟩ ++
        layout.scheme.scalar.representation.encoding.encode ⟨0, zeroValid⟩))) ++ (t ++ [])) ++
          ((r ++ z) ++ ((z ++ n) ++ (m ++ metadataBytes)))
      simp only [List.append_nil, List.append_assoc, List.cons_append, List.nil_append]
      rfl)

theorem finish_buffers : (finish layout zeroValid).code.memBound ≤ 2 :=
  (code_names _ _ (finishOperands_sources layout zeroValid)).2
theorem finish_names (names : Nat) : NamesAccounted (finish layout zeroValid).code names :=
  code_namesAccounted _ _ (finishOperands_sources layout zeroValid)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Signing.Arithmetic
