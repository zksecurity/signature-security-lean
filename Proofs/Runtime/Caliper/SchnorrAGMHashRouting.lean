import Proofs.Runtime.Caliper.SchnorrAGMHashLayout

/-! Executed hash frame routing. Packing copies the chronological basis and
coefficient list before saving the complete current input. Finishing combines
the computed affine pair with the saved key and original source state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
    (layout : Layouts w M F G qH qS)

def inputKey (value : layout.input.Value) : layout.scheme.key.Value := ⟨value.val.1, value.property.1.1⟩
def inputCoefficients (value : layout.input.Value) : layout.flat.attach.values.Value := ⟨value.val.2.1, value.property.1.2.1⟩
def inputState (value : layout.input.Value) : layout.scheme.state.Value := ⟨value.val.2.2, value.property.1.2.2⟩
def inputTable (value : layout.input.Value) : layout.scheme.cache.lookup.table.Value := ⟨value.val.2.2.1, value.property.1.2.2.1⟩
def inputBasis (value : layout.input.Value) : layout.scheme.basis.Value := ⟨value.val.2.2.2.1, value.property.1.2.2.2.1⟩
def inputSignedFlags (value : layout.input.Value) : layout.scheme.signedFlags.Value := ⟨value.val.2.2.2.2, value.property.1.2.2.2.2⟩

theorem input_bytes (value : layout.input.Value) : layout.input.representation.encoding.encode value =
    layout.scheme.key.representation.encoding.encode (inputKey layout value) ++
      (layout.flat.attach.values.representation.encoding.encode (inputCoefficients layout value) ++
        layout.scheme.state.representation.encoding.encode (inputState layout value)) := rfl

theorem state_bytes (value : layout.input.Value) : layout.scheme.state.representation.encoding.encode (inputState layout value) =
    layout.scheme.cache.lookup.table.representation.encoding.encode (inputTable layout value) ++
      (layout.scheme.basis.representation.encoding.encode (inputBasis layout value) ++
        layout.scheme.signedFlags.representation.encoding.encode (inputSignedFlags layout value)) := rfl

def packOperands : List (Operand w) :=
  reads 0 (layout.scheme.key.representation.encoding.words + layout.flat.attach.values.representation.encoding.words +
    layout.scheme.cache.lookup.table.representation.encoding.words) layout.scheme.basis.representation.encoding.words ++
    reads 0 layout.scheme.key.representation.encoding.words layout.flat.attach.values.representation.encoding.words ++
    reads 0 0 layout.input.representation.encoding.words

theorem packOperands_length : (packOperands layout).length = layout.packed.encoding.words := by
  simp only [packOperands, List.length_append, reads_length]
  rfl

theorem packOperands_sources : SourcesBound (packOperands layout) 1 := by
  simp only [packOperands, sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩

def pack : Realizer .unit layout.input.representation layout.packed layout.packValue :=
  Assembly.realizer .unit (by decide) _ _ _ (packOperands layout) layout.scheme.wordFits (packOperands_length layout)
    (by
      intro operand member
      simp only [packOperands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = layout.scheme.key.representation.encoding.words +
        (layout.flat.attach.values.representation.encoding.words +
          (layout.scheme.cache.lookup.table.representation.encoding.words +
            (layout.scheme.basis.representation.encoding.words + layout.scheme.signedFlags.representation.encoding.words))) at size
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact layout.input.representation.fits
      simp only [packOperands, List.mem_append] at member
      rcases member with (member | member) | member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by rw [represented_size _ represented]; omega) fits operand member)
    (by
      intro value before represented
      have contents := represented.2.1
      rw [input_bytes] at contents
      have coefficients := ListFold.reads_block (layout.scheme.key.representation.encoding.encode (inputKey layout value))
        (layout.flat.attach.values.representation.encoding.encode (inputCoefficients layout value))
        (layout.scheme.state.representation.encoding.encode (inputState layout value)) before
        (by simpa only [List.append_assoc] using contents)
      have basis := ListFold.reads_block
        (layout.scheme.key.representation.encoding.encode (inputKey layout value) ++
          layout.flat.attach.values.representation.encoding.encode (inputCoefficients layout value) ++
            layout.scheme.cache.lookup.table.representation.encoding.encode (inputTable layout value))
        (layout.scheme.basis.representation.encoding.encode (inputBasis layout value))
        (layout.scheme.signedFlags.representation.encoding.encode (inputSignedFlags layout value)) before
        (by simpa only [state_bytes, List.append_assoc] using contents)
      have saved := ListFold.reads_block [] (layout.input.representation.encoding.encode value) [] before
        (by simpa using represented.2.1)
      simp only [List.length_append, List.length_nil, Encoding.encode_length] at coefficients basis saved
      simp only [packOperands, values, List.map_append]
      change values (reads 0 _ _) before ++ values (reads 0 _ _) before ++ values (reads 0 0 _) before = _
      rw [basis, coefficients, saved]
      rfl)

variable [Zero F]

def finishOperands : List (Operand w) :=
  reads 0 layout.flat.affine.representation.encoding.words layout.scheme.key.representation.encoding.words ++
    reads 0 0 layout.flat.affine.representation.encoding.words ++
    reads 0 (layout.flat.affine.representation.encoding.words + layout.scheme.key.representation.encoding.words +
      layout.flat.attach.values.representation.encoding.words) layout.scheme.state.representation.encoding.words

theorem finishOperands_length : (finishOperands layout).length = (Read.input layout.scheme).representation.encoding.words := by
  simp only [finishOperands, List.length_append, reads_length]
  change _ = layout.scheme.key.representation.encoding.words +
    (layout.flat.affine.representation.encoding.words + layout.scheme.state.representation.encoding.words)
  omega

omit [Zero F] [DecidableEq M] [DecidableEq G] in
theorem finishOperands_sources : SourcesBound (finishOperands layout) 1 := by
  simp only [finishOperands, sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩

def finish : Realizer .unit layout.flattened (Read.input layout.scheme).representation layout.readValue :=
  Assembly.realizer .unit (by decide) _ _ _ (finishOperands layout) layout.scheme.wordFits (finishOperands_length layout)
    (by
      intro operand member
      simp only [finishOperands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = layout.flat.affine.representation.encoding.words +
        (layout.scheme.key.representation.encoding.words +
          (layout.flat.attach.values.representation.encoding.words + layout.scheme.state.representation.encoding.words)) at size
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact layout.flattened.fits
      simp only [finishOperands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro value before represented
      have contents : (before.bufs 0).toList = layout.flat.affine.representation.encoding.encode value.1 ++
          layout.input.representation.encoding.encode value.2 := represented.2.1
      have affine := ListFold.reads_block [] (layout.flat.affine.representation.encoding.encode value.1)
        (layout.input.representation.encoding.encode value.2) before (by simpa using contents)
      rw [input_bytes] at contents
      have key := ListFold.reads_block (layout.flat.affine.representation.encoding.encode value.1)
        (layout.scheme.key.representation.encoding.encode (inputKey layout value.2))
        (layout.flat.attach.values.representation.encoding.encode (inputCoefficients layout value.2) ++
          layout.scheme.state.representation.encoding.encode (inputState layout value.2)) before
        (by simpa only [List.append_assoc] using contents)
      have state := ListFold.reads_block
        (layout.flat.affine.representation.encoding.encode value.1 ++
          layout.scheme.key.representation.encoding.encode (inputKey layout value.2) ++
            layout.flat.attach.values.representation.encoding.encode (inputCoefficients layout value.2))
        (layout.scheme.state.representation.encoding.encode (inputState layout value.2)) [] before
        (by simpa only [List.append_nil, List.append_assoc] using contents)
      simp only [List.length_append, List.length_nil, Encoding.encode_length] at affine key state
      simp only [finishOperands, values, List.map_append]
      change values (reads 0 _ _) before ++ values (reads 0 0 _) before ++ values (reads 0 _ _) before = _
      rw [key, affine, state]
      change (_ ++ _) ++ _ = _ ++ (_ ++ _)
      exact List.append_assoc _ _ _)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Hash
