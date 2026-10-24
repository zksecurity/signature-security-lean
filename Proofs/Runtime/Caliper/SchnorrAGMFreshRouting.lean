import Proofs.Runtime.Caliper.SchnorrAGMFreshLayout

/-! Paid frame construction for the fresh-entry arithmetic. These programs
read the challenge, affine coefficients and old flag from runtime buffer zero. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def constant (value : Input layout) : layout.scalar.Value :=
  ⟨value.2.val.1.1, value.2.property.1.1⟩
def secret (value : Input layout) : layout.scalar.Value :=
  ⟨value.2.val.1.2, value.2.property.1.2⟩

theorem input_bytes (value : Input layout) : (input layout).encoding.encode value =
    layout.scalar.representation.encoding.encode value.1 ++
      ((layout.scalar.representation.encoding.encode (constant layout value) ++
        layout.scalar.representation.encoding.encode (secret layout value)) ++
          [if value.2.val.2 then 1 else 0]) := rfl

def addOperands : List (Operand w) :=
  reads 0 (2 * layout.scalar.representation.encoding.words) layout.scalar.representation.encoding.words ++
    reads 0 0 layout.scalar.representation.encoding.words ++ reads 0 0 (input layout).encoding.words

theorem addOperands_length : (addOperands layout).length = (adding layout).encoding.words := by
  simp only [addOperands, List.length_append, reads_length]
  change _ + _ + _ = layout.affine.representation.encoding.words + _
  rw [Layouts.affine_words]; omega

theorem addOperands_sources : SourcesBound (addOperands layout) 1 := by
  simp only [addOperands, sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩

def prepareAdd : Realizer .unit (input layout) (adding layout) (addValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (addOperands layout) layout.wordFits (addOperands_length layout)
    (by
      intro operand member
      simp only [addOperands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      rw [input_words] at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact (input layout).fits
      simp only [addOperands, List.mem_append] at member
      rcases member with (member | member) | member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by rw [input_words]; omega) fits operand member)
    (by
      intro value before represented
      have contents := represented.2.1
      rw [input_bytes] at contents
      have first := ListFold.reads_block
        (layout.scalar.representation.encoding.encode value.1 ++
          layout.scalar.representation.encoding.encode (constant layout value))
        (layout.scalar.representation.encoding.encode (secret layout value))
        [if value.2.val.2 then 1 else 0] before (by simpa only [List.append_assoc] using contents)
      have second := ListFold.reads_block [] (layout.scalar.representation.encoding.encode value.1)
        ((layout.scalar.representation.encoding.encode (constant layout value) ++
          layout.scalar.representation.encoding.encode (secret layout value)) ++
            [if value.2.val.2 then 1 else 0]) before (by simpa using contents)
      have all := ListFold.reads_block [] ((input layout).encoding.encode value) [] before
        (by simpa using represented.2.1)
      simp only [List.length_append, Encoding.encode_length, List.length_nil] at first second all
      have twice : layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words =
          2 * layout.scalar.representation.encoding.words := by omega
      rw [twice] at first
      change values (reads 0 0 _) before = _ at second all
      simp only [addOperands, values, List.map_append]
      change values (reads 0 (2 * _) _) before ++ values (reads 0 0 _) before ++ values (reads 0 0 _) before = _
      rw [first, second, all]
      rfl)

def mergeOperands : List (Operand w) :=
  reads 0 (1 + 3 * layout.scalar.representation.encoding.words) 1 ++ reads 0 0 1 ++
    reads 0 1 (input layout).encoding.words

theorem mergeOperands_length : (mergeOperands layout).length = (merging layout).encoding.words := by
  simp only [mergeOperands, List.length_append, reads_length]
  rfl

theorem mergeOperands_sources : SourcesBound (mergeOperands layout) 1 := by
  simp only [mergeOperands, sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩

def prepareMerge : Realizer .unit (flagged layout) (merging layout) (mergeValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (mergeOperands layout) layout.wordFits (mergeOperands_length layout)
    (by
      intro operand member
      simp only [mergeOperands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = 1 + (input layout).encoding.words at size
      rw [input_words] at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact (flagged layout).fits
      simp only [mergeOperands, List.mem_append] at member
      rcases member with (member | member) | member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by rw [input_words]; omega) fits operand member)
    (by
      intro value before represented
      have contents : (before.bufs 0).toList =
          [if value.1 then 1 else 0] ++ (input layout).encoding.encode value.2 := represented.2.1
      have old := ListFold.reads_block
        ([if value.1 then 1 else 0] ++ layout.scalar.representation.encoding.encode value.2.1 ++
          layout.scalar.representation.encoding.encode (constant layout value.2) ++
          layout.scalar.representation.encoding.encode (secret layout value.2))
        [if value.2.2.val.2 then 1 else 0] [] before (by
          simpa only [input_bytes, List.append_assoc, List.append_nil] using contents)
      have flag := ListFold.reads_block [] [if value.1 then 1 else 0]
        ((input layout).encoding.encode value.2) before (by simpa using contents)
      have saved := ListFold.reads_block [if value.1 then 1 else 0]
        ((input layout).encoding.encode value.2) [] before (by simpa using contents)
      simp only [List.length_append, Encoding.encode_length, List.length_cons, List.length_nil] at old flag saved
      have offset : 1 + layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words +
          layout.scalar.representation.encoding.words = 1 + 3 * layout.scalar.representation.encoding.words := by omega
      rw [offset] at old
      simp only [mergeOperands, values, List.map_append]
      change values (reads 0 (1 + 3 * _) 1) before ++ values (reads 0 0 1) before ++ values (reads 0 1 _) before = _
      rw [old, flag, saved]
      rfl)

def finishOperands : List (Operand w) :=
  reads 0 1 layout.scalar.representation.encoding.words ++ [.literal 1] ++
    reads 0 (1 + layout.scalar.representation.encoding.words) (2 * layout.scalar.representation.encoding.words) ++
    reads 0 (1 + layout.scalar.representation.encoding.words) (2 * layout.scalar.representation.encoding.words) ++
    reads 0 0 1

theorem finishOperands_length : (finishOperands layout).length = (Cache.model layout).freshOutput.encoding.words := by
  simp only [finishOperands, List.length_append, reads_length, List.length_cons, List.length_nil]
  change _ = layout.entry.representation.encoding.words + (layout.affine.representation.encoding.words + 1)
  rw [Layouts.entry_words, Layouts.affine_words]; omega

theorem finishOperands_sources : SourcesBound (finishOperands layout) 1 := by
  simp only [finishOperands, sourcesBound_append]
  exact ⟨⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), by simp⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩

def finish : Realizer .unit (flagged layout) (Cache.model layout).freshOutput (finishValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (finishOperands layout) layout.wordFits (finishOperands_length layout)
    (by
      intro operand member
      simp only [finishOperands, List.mem_append] at member
      rcases member with (((member | member) | member) | member) | member
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · simp only [List.mem_singleton] at member; subst operand; trivial
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · exact reads_namesFit 0 _ _ (by positivity) operand member
      · exact reads_namesFit 0 _ _ (by positivity) operand member)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = 1 + (input layout).encoding.words at size
      rw [input_words] at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact (flagged layout).fits
      simp only [finishOperands, List.mem_append] at member
      rcases member with (((member | member) | member) | member) | member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · simp only [List.mem_singleton] at member; subst operand; trivial
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro value before represented
      have contents : (before.bufs 0).toList =
          [if value.1 then 1 else 0] ++ (input layout).encoding.encode value.2 := represented.2.1
      have challenge := ListFold.reads_block [if value.1 then 1 else 0]
        (layout.scalar.representation.encoding.encode value.2.1)
        ((layout.scalar.representation.encoding.encode (constant layout value.2) ++
          layout.scalar.representation.encoding.encode (secret layout value.2)) ++
            [if value.2.2.val.2 then 1 else 0]) before (by
          simpa only [input_bytes, List.append_assoc] using contents)
      have affine := ListFold.reads_block
        ([if value.1 then 1 else 0] ++ layout.scalar.representation.encoding.encode value.2.1)
        (layout.scalar.representation.encoding.encode (constant layout value.2) ++
          layout.scalar.representation.encoding.encode (secret layout value.2))
        [if value.2.2.val.2 then 1 else 0] before (by
          simpa only [input_bytes, List.append_assoc] using contents)
      have flag := ListFold.reads_block [] [if value.1 then 1 else 0]
        ((input layout).encoding.encode value.2) before (by simpa using contents)
      simp only [List.length_append, Encoding.encode_length, List.length_cons, List.length_nil] at challenge affine flag
      have twice : layout.scalar.representation.encoding.words + layout.scalar.representation.encoding.words =
          2 * layout.scalar.representation.encoding.words := by omega
      rw [twice] at affine
      simp only [finishOperands, values, List.map_append]
      change values (reads 0 1 _) before ++ [1] ++ values (reads 0 (1 + _) _) before ++
        values (reads 0 (1 + _) _) before ++ values (reads 0 0 1) before = _
      rw [challenge, affine, flag]
      change _ = (layout.scalar.representation.encoding.encode value.2.1 ++
        ([1] ++ (layout.scalar.representation.encoding.encode (constant layout value.2) ++
          layout.scalar.representation.encoding.encode (secret layout value.2)))) ++
        ((layout.scalar.representation.encoding.encode (constant layout value.2) ++
          layout.scalar.representation.encoding.encode (secret layout value.2)) ++ [if value.1 then 1 else 0])
      simp only [List.append_assoc])

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
