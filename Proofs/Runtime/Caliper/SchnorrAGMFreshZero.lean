import Proofs.Runtime.Caliper.SchnorrAGMFreshRouting

/-! Zero testing uses a stored encoding of zero and scans the scalar's words.
The zero constant, its copies and the equality program are all charged. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} [Zero F] [DecidableEq F]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)

def zeroPair : Representation w (layout.scalar.Value × layout.scalar.Value) :=
  layout.scalar.representation.prod layout.scalar.representation layout.affine.representation.fits

def zeroOperands : List (Operand w) :=
  reads 0 0 layout.scalar.representation.encoding.words ++
    (layout.scalar.representation.encoding.encode ⟨0, zeroValid⟩).map Operand.literal

omit [DecidableEq F] in
theorem zeroOperands_length : (zeroOperands layout zeroValid).length = (zeroPair layout).encoding.words := by
  simp only [zeroOperands, List.length_append, reads_length, List.length_map, Encoding.encode_length]
  rfl

omit [DecidableEq F] in
theorem zeroOperands_sources : SourcesBound (zeroOperands layout zeroValid) 1 := by
  apply (sourcesBound_append _ _ _).mpr
  refine ⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

def prepareZero : Realizer .unit layout.scalar.representation (zeroPair layout)
    (fun value => (value, ⟨0, zeroValid⟩)) :=
  Assembly.realizer .unit (by decide) _ _ _ (zeroOperands layout zeroValid) layout.wordFits
    (zeroOperands_length layout zeroValid)
    (by
      intro operand member
      rcases List.mem_append.mp member with copied | literal
      · exact reads_namesFit _ _ _ (by positivity) operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial)
    (by
      intro value before represented operand member
      rcases List.mem_append.mp member with copied | literal
      · exact reads_valid 1 0 0 _ before (by decide)
          (by rw [represented_size _ represented]; omega)
          (by rw [represented_size _ represented]; exact layout.scalar.representation.fits) operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial)
    (by
      intro value before represented
      have copied := ListFold.reads_block [] (layout.scalar.representation.encoding.encode value) []
        before (by simpa using represented.2.1)
      simp only [List.length_nil, Encoding.encode_length] at copied
      simp only [zeroOperands, values, List.map_append, List.map_map]
      change values (reads 0 0 _) before ++ _ = _
      rw [copied]
      exact congrArg (List.append _) (List.map_id _))

def isZero : Realizer .unit layout.scalar.representation
    (Representation.boolean w (width_pos layout.wordFits)) (fun value => decide (value.val = 0)) :=
  ((prepareZero layout zeroValid).then
    (EncodedEquality.realizer .unit layout.scalar.representation layout.wordFits
      layout.affine.representation.fits)).viewOutput _ (fun value => decide (value.val = 0)) (by
        intro value
        change [if decide (value.val = 0) then 1 else 0] =
          [if decide (value = (⟨0, zeroValid⟩ : layout.scalar.Value)) then 1 else 0]
        simp only [Subtype.ext_iff])

theorem zero_time (value : layout.scalar.Value) :
    (isZero layout zeroValid).time value ≤ 22 * layout.scalar.representation.encoding.words + 3 := by
  have copied := code_time_unit_le (zeroOperands layout zeroValid)
  rw [zeroOperands_length] at copied
  change _ ≤ 8 * (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) at copied
  have equality := EncodedEquality.time_unit layout.scalar.representation.encoding.words
  change (Assembly.code (zeroOperands layout zeroValid)).staticTime .unit +
    EncodedEquality.time .unit layout.scalar.representation.encoding.words ≤ _
  omega

theorem zero_words : descriptionWords (isZero layout zeroValid).code ≤
    82 * layout.scalar.representation.encoding.words + 28 := by
  have copied := code_descriptionWords_le (zeroOperands layout zeroValid)
  rw [zeroOperands_length] at copied
  change _ ≤ 26 * (layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words) + 14 at copied
  change descriptionWords (Assembly.code (zeroOperands layout zeroValid) ;;
    EncodedEquality.code layout.scalar.representation.encoding.words) ≤ _
  rw [descriptionWords_seq, EncodedEquality.code_descriptionWords]
  omega

theorem zero_names : NamesBound (isZero layout zeroValid).code 5 := by
  have copied := code_names (zeroOperands layout zeroValid) 1 (zeroOperands_sources layout zeroValid)
  have equality := EncodedEquality.code_names (w := w) layout.scalar.representation.encoding.words
  exact ⟨max_le (copied.1.trans (by decide)) equality.registers,
    max_le (copied.2.trans (by decide)) equality.buffers⟩

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
