import Signatures.Runtime.Caliper.SchnorrROMSigningLayout

/-! Signing arithmetic arguments are copied from the sampled request. The
two group multiplications receive `(z, g)` and `(c, pk)` in that order. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Arithmetic
open Caliper BoundedSource Assembly
variable {w : Nat} {M F G : Type} (layout : Layouts w M F G)

def challenge (value : layout.input.Value) : layout.scalar.Value := ⟨value.val.1.1, value.property.1.1.1⟩
def response (value : layout.input.Value) : layout.scalar.Value := ⟨value.val.1.2, value.property.1.1.2⟩
def generator (value : layout.input.Value) : layout.point.Value := ⟨value.val.2.1, value.property.1.2.1⟩
def publicKey (value : layout.input.Value) : layout.point.Value := ⟨value.val.2.2.1, value.property.1.2.2.1⟩
def inputTail (value : layout.input.Value) : layout.messageTable.Value := ⟨value.val.2.2.2, value.property.1.2.2.2⟩

theorem input_bytes (value : layout.input.Value) : layout.input.representation.encoding.encode value =
    (layout.scalar.representation.encoding.encode (challenge layout value) ++
      layout.scalar.representation.encoding.encode (response layout value)) ++
        (layout.point.representation.encoding.encode (generator layout value) ++
          (layout.point.representation.encoding.encode (publicKey layout value) ++
            layout.messageTable.representation.encoding.encode (inputTail layout value))) := rfl

variable [Zero F] (zeroValid : layout.scalar.valid 0)

def argumentValue (value : Input M F G) : (F × F) × F × G × G :=
  ((value.1.2, value.1.1), 0, value.2.2.1, value.2.1)
def argumentOperands : List (Operand w) :=
  reads 0 layout.scalar.representation.encoding.words layout.scalar.representation.encoding.words ++
    reads 0 0 layout.scalar.representation.encoding.words ++
    (layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩).map Operand.literal ++
    reads 0 (2 * layout.scalar.representation.encoding.words + layout.point.representation.encoding.words)
      layout.point.representation.encoding.words ++
    reads 0 (2 * layout.scalar.representation.encoding.words) layout.point.representation.encoding.words

theorem argumentOperands_length : (argumentOperands layout zeroValid).length = layout.arithmetic.badInput.representation.encoding.words := by
  simp only [argumentOperands, List.length_append, reads_length, List.length_map, Encoding.encode_length]
  change _ = (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) +
    (layout.scalar.representation.encoding.words +
      (layout.point.representation.encoding.words + layout.point.representation.encoding.words))
  omega
theorem argumentOperands_sources : SourcesBound (argumentOperands layout zeroValid) 1 := by
  simp only [argumentOperands, sourcesBound_append]
  refine ⟨⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩, ?_⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

def arguments : Implementation .unit layout.input layout.arithmetic.badInput argumentValue where
  preserves _ valid := ⟨⟨valid.1.1.2, valid.1.1.1⟩, zeroValid, valid.1.2.2.1, valid.1.2.1⟩
  program := Assembly.realizer .unit (by decide) _ _ _ (argumentOperands layout zeroValid) layout.wordFits
    (argumentOperands_length layout zeroValid)
    (by
      intro operand member
      simp only [argumentOperands, List.mem_append] at member
      rcases member with (((copied | copied) | literal) | copied) | copied
      · exact reads_namesFit 0 _ _ (by positivity) operand copied
      · exact reads_namesFit 0 _ _ (by positivity) operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
      · exact reads_namesFit 0 _ _ (by positivity) operand copied
      · exact reads_namesFit 0 _ _ (by positivity) operand copied)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      rw [layout.input_words] at size
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact layout.input.representation.fits
      simp only [argumentOperands, List.mem_append] at member
      rcases member with (((copied | copied) | literal) | copied) | copied
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied)
    (by
      intro value before represented
      have contents := represented.2.1
      rw [input_bytes] at contents
      have c := ListFold.reads_block [] (layout.scalar.representation.encoding.encode (challenge layout value))
        (layout.scalar.representation.encoding.encode (response layout value) ++
          (layout.point.representation.encoding.encode (generator layout value) ++
            (layout.point.representation.encoding.encode (publicKey layout value) ++
              layout.messageTable.representation.encoding.encode (inputTail layout value)))) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have z := ListFold.reads_block (layout.scalar.representation.encoding.encode (challenge layout value))
        (layout.scalar.representation.encoding.encode (response layout value))
        (layout.point.representation.encoding.encode (generator layout value) ++
          (layout.point.representation.encoding.encode (publicKey layout value) ++
            layout.messageTable.representation.encoding.encode (inputTail layout value))) before contents
      have g := ListFold.reads_block
        (layout.scalar.representation.encoding.encode (challenge layout value) ++
          layout.scalar.representation.encoding.encode (response layout value))
        (layout.point.representation.encoding.encode (generator layout value))
        (layout.point.representation.encoding.encode (publicKey layout value) ++
          layout.messageTable.representation.encoding.encode (inputTail layout value)) before
        (by simpa only [List.append_assoc] using contents)
      have pk := ListFold.reads_block
        (layout.scalar.representation.encoding.encode (challenge layout value) ++
          layout.scalar.representation.encoding.encode (response layout value) ++
            layout.point.representation.encoding.encode (generator layout value))
        (layout.point.representation.encoding.encode (publicKey layout value))
        (layout.messageTable.representation.encoding.encode (inputTail layout value)) before
        (by simpa only [List.append_assoc] using contents)
      simp only [List.length_nil, List.length_append, Encoding.encode_length] at c z g pk
      rw [show layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words =
        2 * layout.scalar.representation.encoding.words by omega] at g pk
      simp only [argumentOperands, values, List.map_append, List.map_map]
      change values (reads 0 _ _) before ++ values (reads 0 0 _) before ++ _ ++ values (reads 0 _ _) before ++ values (reads 0 _ _) before = _
      rw [z, c, pk, g]
      rw [show Operand.value before ∘ Operand.literal = id from rfl, List.map_id]
      change _ = (layout.scalar.representation.encoding.encode (response layout value) ++
        layout.scalar.representation.encoding.encode (challenge layout value)) ++
          (layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩ ++
            (layout.point.representation.encoding.encode (publicKey layout value) ++
              layout.point.representation.encoding.encode (generator layout value)))
      simp only [List.append_assoc])

theorem arguments_bounded : (arguments layout zeroValid).BoundedBy
    (8 * layout.arithmetic.badInput.representation.encoding.words) (26 * layout.arithmetic.badInput.representation.encoding.words + 14) := by
  constructor
  · intro value
    have bounded := code_time_unit_le (argumentOperands layout zeroValid)
    rw [argumentOperands_length] at bounded
    exact bounded
  · have bounded := code_descriptionWords_le (argumentOperands layout zeroValid)
    rw [argumentOperands_length] at bounded
    exact bounded
theorem arguments_names (slots : Nat) : NamesAccounted (arguments layout zeroValid).program.code slots :=
  code_namesAccounted _ _ (argumentOperands_sources layout zeroValid)
theorem arguments_buffers : (arguments layout zeroValid).program.code.memBound ≤ 2 :=
  (code_names _ _ (argumentOperands_sources layout zeroValid)).2

end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing.Arithmetic
