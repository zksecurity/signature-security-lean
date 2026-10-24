import Proofs.Runtime.Caliper.SchnorrAGMHashShape

/-! After the executed singleton test, copy the actual message, point, scalar
row and state into the hash core's input frame. Unused list capacity is dropped
by actual copying, while the selected coefficient row keeps its own capacity. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS)

def original (value : layout.yes.Value) : layout.input.Value := ⟨value.val, value.property.1⟩
def acceptedPoint (value : layout.yes.Value) : layout.hash.scheme.point.Value :=
  ⟨layout.point value, value.property.1.1.2.1.2 _ (List.getElem_mem _)⟩
def acceptedRow (value : layout.yes.Value) : layout.hash.flat.attach.values.Value :=
  Hash.inputCoefficients layout.hash (layout.acceptedValue value)

def acceptOperands : List (Operand w) :=
  reads 0 0 layout.hash.scheme.message.representation.encoding.words ++
    reads 0 (layout.hash.scheme.message.representation.encoding.words + 1) layout.hash.scheme.point.representation.encoding.words ++
    reads 0 (layout.hash.scheme.message.representation.encoding.words + layout.points.representation.encoding.words + 1)
      layout.hash.flat.attach.values.representation.encoding.words ++
    reads 0 (layout.hash.scheme.message.representation.encoding.words + layout.points.representation.encoding.words +
      layout.coefficients.representation.encoding.words) layout.hash.scheme.state.representation.encoding.words

theorem acceptOperands_length : (acceptOperands layout).length = layout.hash.input.representation.encoding.words := by
  simp only [acceptOperands, List.length_append, reads_length]
  change (_ + _ + _) + _ = (_ + _) + (_ + _)
  omega

omit [DecidableEq M] [DecidableEq G] in
theorem acceptOperands_sources : SourcesBound (acceptOperands layout) 1 := by
  simp only [acceptOperands, sourcesBound_append]
  exact ⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩

def accept : Realizer .unit layout.yes.representation layout.hash.input.representation layout.acceptedValue :=
  Assembly.realizer .unit (by decide) _ _ _ (acceptOperands layout) layout.hash.scheme.wordFits (acceptOperands_length layout)
    (by
      intro operand member
      simp only [acceptOperands, List.mem_append] at member
      rcases member with ((member | member) | member) | member <;>
        exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = layout.input.representation.encoding.words at size
      rw [layout.input_words] at size
      have lengths := layout.lengths value
      have pointCapacity : 1 ≤ layout.groups := by have := value.property.1.1.2.1.1; omega
      have rowCapacity : 1 ≤ layout.rows := by have := value.property.1.1.2.2.1.1; omega
      have pointSize := Nat.mul_le_mul_right layout.hash.scheme.point.representation.encoding.words pointCapacity
      have rowSize := Nat.mul_le_mul_right layout.hash.flat.attach.values.representation.encoding.words rowCapacity
      simp only [Nat.one_mul] at pointSize rowSize
      have pointWords : layout.points.representation.encoding.words = 1 + layout.groups * layout.hash.scheme.point.representation.encoding.words := rfl
      have rowWords : layout.coefficients.representation.encoding.words = 1 + layout.rows * layout.hash.flat.attach.values.representation.encoding.words := rfl
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact layout.yes.representation.fits
      simp only [acceptOperands, List.mem_append] at member
      rcases member with ((member | member) | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro value before represented
      let source := original layout value
      have contents : (before.bufs 0).toList = layout.input.representation.encoding.encode source := represented.2.1
      rw [input_bytes] at contents
      have message := ListFold.reads_block []
        (layout.hash.scheme.message.representation.encoding.encode (inputMessage layout source))
        (layout.points.representation.encoding.encode (inputPoints layout source) ++
          (layout.coefficients.representation.encoding.encode (inputRows layout source) ++
            layout.hash.scheme.state.representation.encoding.encode (inputState layout source))) before
        (by simpa only [List.nil_append] using contents)
      have point := ListBytes.read_singleton layout.hash.scheme.point layout.groups layout.groupCountFits layout.points.representation.fits
        (inputPoints layout source) (acceptedPoint layout value) (layout.points_singleton value)
        (layout.hash.scheme.message.representation.encoding.encode (inputMessage layout source))
        (layout.coefficients.representation.encoding.encode (inputRows layout source) ++
          layout.hash.scheme.state.representation.encoding.encode (inputState layout source)) before contents
      have row := ListBytes.read_singleton layout.hash.flat.attach.values layout.rows layout.rowCountFits layout.coefficients.representation.fits
        (inputRows layout source) (acceptedRow layout value) (layout.rows_singleton value)
        (layout.hash.scheme.message.representation.encoding.encode (inputMessage layout source) ++
          layout.points.representation.encoding.encode (inputPoints layout source))
        (layout.hash.scheme.state.representation.encoding.encode (inputState layout source)) before (by
          change (before.bufs 0).toList = (_ ++ _) ++
            (layout.coefficients.representation.encoding.encode (inputRows layout source) ++ _)
          simpa only [List.append_assoc] using contents)
      have state := ListFold.reads_block
        (layout.hash.scheme.message.representation.encoding.encode (inputMessage layout source) ++
          layout.points.representation.encoding.encode (inputPoints layout source) ++
            layout.coefficients.representation.encoding.encode (inputRows layout source))
        (layout.hash.scheme.state.representation.encoding.encode (inputState layout source)) [] before
        (by simpa only [List.append_assoc, List.append_nil] using contents)
      simp only [List.length_nil, List.length_append, Encoding.encode_length] at message point row state
      simp only [acceptOperands, values, List.map_append]
      change values (reads 0 0 _) before ++ values (reads 0 _ _) before ++ values (reads 0 _ _) before ++ values (reads 0 _ _) before = _
      rw [message, point, row, state]
      change ((_ ++ _) ++ _) ++ _ = (_ ++ _) ++ (_ ++ _)
      rw [List.append_assoc]
      rfl)

theorem accept_time (value : layout.yes.Value) :
    (accept layout).time value ≤ 8 * layout.hash.input.representation.encoding.words := by
  have bound := code_time_unit_le (acceptOperands layout)
  rw [acceptOperands_length] at bound
  exact bound
theorem accept_words : descriptionWords (accept layout).code ≤ 26 * layout.hash.input.representation.encoding.words + 14 := by
  have bound := code_descriptionWords_le (acceptOperands layout)
  rw [acceptOperands_length] at bound
  exact bound
theorem accept_names (slots : Nat) : NamesAccounted (accept layout).code slots :=
  code_namesAccounted _ _ (acceptOperands_sources layout)
theorem accept_buffers : (accept layout).code.memBound ≤ 2 :=
  (code_names _ _ (acceptOperands_sources layout)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
