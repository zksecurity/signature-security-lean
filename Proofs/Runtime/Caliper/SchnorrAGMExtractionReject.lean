import Proofs.Runtime.Caliper.SchnorrAGMHashShape
import Proofs.Runtime.Caliper.SchnorrAGMEntryReadMemory

/-! A malformed final forgery produces an unexplained entry, so the scalar
terminal returns zero. Its private state is copied unchanged, including both
flags. This differs from rejection of a malformed hash query. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionEntry
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} (layout : HashDispatch.Layouts w M F G qH qS)
    [Zero F] (zeroValid : layout.hash.scheme.scalar.valid 0)

def emptyEntry : layout.hash.scheme.entry.Value := ⟨(0, false, 0, 0), zeroValid, trivial, zeroValid, zeroValid⟩
def stateOffset : Nat := layout.hash.scheme.message.representation.encoding.words + layout.points.representation.encoding.words +
  layout.coefficients.representation.encoding.words
def rejectOperands : List (Operand w) :=
  (layout.hash.scheme.entry.representation.encoding.encode (emptyEntry layout zeroValid)).map Operand.literal ++
    reads 0 (stateOffset layout) layout.hash.scheme.state.representation.encoding.words
theorem rejectOperands_length : (rejectOperands layout zeroValid).length =
    (EntryRead.output layout.hash.scheme).representation.encoding.words := by
  simp only [rejectOperands, List.length_append, List.length_map, Encoding.encode_length, reads_length]
  rfl
theorem rejectOperands_sources : SourcesBound (rejectOperands layout zeroValid) 1 := by
  rw [rejectOperands, sourcesBound_append]
  refine ⟨?_, sourcesBound_reads _ _ _ _ (by decide)⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial

variable [DecidableEq M] [DecidableEq G]
def rejectValue (value : layout.input.Value) : (EntryRead.output layout.hash.scheme).Value :=
  ⟨((emptyEntry layout zeroValid).val, value.val.2.2.2), (emptyEntry layout zeroValid).property, value.property.1.2.2.2⟩

def reject : Realizer .unit layout.input.representation (EntryRead.output layout.hash.scheme).representation
    (rejectValue layout zeroValid) :=
  Assembly.realizer .unit (by decide) _ _ _ (rejectOperands layout zeroValid) layout.hash.scheme.wordFits
    (rejectOperands_length layout zeroValid)
    (by
      intro operand member
      rcases List.mem_append.mp member with literal | copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
      · exact reads_namesFit 0 _ _ (by positivity) operand copied)
    (by
      intro value before represented operand member
      rcases List.mem_append.mp member with literal | copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
      · have size := represented_size _ represented
        rw [layout.input_words] at size
        exact reads_valid 1 0 _ _ before (by decide) (by unfold stateOffset; omega)
          (by rw [represented_size _ represented]; exact layout.input.representation.fits) operand copied)
    (by
      intro value before represented
      let leading := layout.hash.scheme.message.representation.encoding.encode (HashDispatch.inputMessage layout value) ++
        layout.points.representation.encoding.encode (HashDispatch.inputPoints layout value) ++
          layout.coefficients.representation.encoding.encode (HashDispatch.inputRows layout value)
      have copied := ListFold.reads_block leading
        (layout.hash.scheme.state.representation.encoding.encode (HashDispatch.inputState layout value)) [] before
        (by
          have contents := represented.2.1
          rw [HashDispatch.input_bytes] at contents
          simpa only [leading, List.append_assoc, List.append_nil] using contents)
      simp only [leading, List.length_append, Encoding.encode_length] at copied
      change values (rejectOperands layout zeroValid) before =
        layout.hash.scheme.entry.representation.encoding.encode (emptyEntry layout zeroValid) ++
          layout.hash.scheme.state.representation.encoding.encode (HashDispatch.inputState layout value)
      simp only [rejectOperands, values, List.map_append, List.map_map]
      change _ ++ values (reads 0 (stateOffset layout) _) before = _
      rw [stateOffset, copied]
      exact congrArg (fun bytes => bytes ++ _) (List.map_id _))

theorem reject_time (value : layout.input.Value) :
    (reject layout zeroValid).time value ≤ 8 * (EntryRead.output layout.hash.scheme).representation.encoding.words := by
  have bound := code_time_unit_le (rejectOperands layout zeroValid)
  rw [rejectOperands_length] at bound
  exact bound
theorem reject_words : descriptionWords (reject layout zeroValid).code ≤
    26 * (EntryRead.output layout.hash.scheme).representation.encoding.words + 14 := by
  have bound := code_descriptionWords_le (rejectOperands layout zeroValid)
  rw [rejectOperands_length] at bound
  exact bound
theorem reject_names (slots : Nat) : NamesAccounted (reject layout zeroValid).code slots :=
  code_namesAccounted _ _ (rejectOperands_sources layout zeroValid)
theorem reject_buffers : (reject layout zeroValid).code.memBound ≤ 2 :=
  (code_names _ _ (rejectOperands_sources layout zeroValid)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.ExtractionEntry
