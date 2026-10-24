import Proofs.Runtime.Caliper.SchnorrAGMHashShape

/-! Malformed hash rejection writes a stored scalar zero and sets malformed.
It copies the cache, basis and signing history, preserving the previous bad
flag. The routine is deterministic and contains no sampling instruction. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} (layout : Layouts w M F G qH qS)

def statePrefix (value : layout.hash.scheme.state.Value) : List (Word w) :=
  layout.hash.scheme.cache.lookup.table.representation.encoding.encode ⟨value.val.1, value.property.1⟩ ++
    layout.hash.scheme.basis.representation.encoding.encode ⟨value.val.2.1, value.property.2.1⟩ ++
      layout.hash.scheme.signed.representation.encoding.encode ⟨value.val.2.2.1, value.property.2.2.1⟩
def statePrefixWords : Nat := layout.hash.scheme.cache.lookup.table.representation.encoding.words +
  layout.hash.scheme.basis.representation.encoding.words + layout.hash.scheme.signed.representation.encoding.words
theorem statePrefix_length (value : layout.hash.scheme.state.Value) :
    (statePrefix layout value).length = statePrefixWords layout := by
  simp only [statePrefix, statePrefixWords, List.length_append, Encoding.encode_length]
theorem statePrefix_bytes (value : layout.hash.scheme.state.Value) :
    layout.hash.scheme.state.representation.encoding.encode value = statePrefix layout value ++
      [if value.val.2.2.2.1 then 1 else 0, if value.val.2.2.2.2 then 1 else 0] := by
  change _ ++ (_ ++ (_ ++ ([if value.val.2.2.2.1 then 1 else 0] ++ [if value.val.2.2.2.2 then 1 else 0]))) = _
  simp only [statePrefix, List.append_assoc]
  rfl
theorem statePrefix_words : layout.hash.scheme.state.representation.encoding.words = statePrefixWords layout + 2 := by
  change _ + (_ + (_ + (1 + 1))) = (_ + _ + _) + 2
  omega

def stateOffset : Nat := layout.hash.scheme.message.representation.encoding.words + layout.points.representation.encoding.words +
  layout.coefficients.representation.encoding.words

variable [DecidableEq M] [DecidableEq G] [Zero F] (zeroValid : layout.hash.scheme.scalar.valid 0)

def rejectValue (value : layout.input.Value) : (Read.output layout.hash.scheme).Value :=
  ⟨(0, value.val.2.2.2.1, value.val.2.2.2.2.1, value.val.2.2.2.2.2.1, true, value.val.2.2.2.2.2.2.2),
    zeroValid, value.property.1.2.2.2.1, value.property.1.2.2.2.2.1, value.property.1.2.2.2.2.2.1, trivial,
    value.property.1.2.2.2.2.2.2.2⟩

def rejectOperands : List (Operand w) :=
  (layout.hash.scheme.scalar.representation.encoding.encode ⟨0, zeroValid⟩).map Operand.literal ++
    reads 0 (stateOffset layout) (statePrefixWords layout) ++ [.literal 1] ++
      reads 0 (stateOffset layout + statePrefixWords layout + 1) 1

omit [DecidableEq M] [DecidableEq G] in
theorem rejectOperands_length : (rejectOperands layout zeroValid).length = (Read.output layout.hash.scheme).representation.encoding.words := by
  simp only [rejectOperands, List.length_append, List.length_map, Encoding.encode_length, reads_length, List.length_cons, List.length_nil]
  change _ = layout.hash.scheme.scalar.representation.encoding.words + layout.hash.scheme.state.representation.encoding.words
  rw [statePrefix_words]; omega

omit [DecidableEq M] [DecidableEq G] in
theorem rejectOperands_sources : SourcesBound (rejectOperands layout zeroValid) 1 := by
  simp only [rejectOperands, sourcesBound_append]
  refine ⟨⟨⟨?_, sourcesBound_reads _ _ _ _ (by decide)⟩, ?_⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
  · intro operand member
    obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
    trivial
  · intro operand member
    simp only [List.mem_singleton] at member
    subst operand
    trivial

theorem reject_bytes (value : layout.input.Value) :
    (Read.output layout.hash.scheme).representation.encoding.encode (rejectValue layout zeroValid value) =
      layout.hash.scheme.scalar.representation.encoding.encode ⟨0, zeroValid⟩ ++
        statePrefix layout (inputState layout value) ++ [1] ++ [if value.val.2.2.2.2.2.2.2 then 1 else 0] := by
  change _ ++ (_ ++ (_ ++ (_ ++ ([1] ++ [if value.val.2.2.2.2.2.2.2 then 1 else 0])))) = _
  simp only [statePrefix, List.append_assoc]
  rfl

def reject : Realizer .unit layout.input.representation (Read.output layout.hash.scheme).representation (rejectValue layout zeroValid) :=
  Assembly.realizer .unit (by decide) _ _ _ (rejectOperands layout zeroValid) layout.hash.scheme.wordFits (rejectOperands_length layout zeroValid)
    (by
      intro operand member
      simp only [rejectOperands, List.mem_append, List.mem_singleton] at member
      rcases member with ((literal | copied) | rfl) | copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
      · exact reads_namesFit 0 _ _ (by positivity) operand copied
      · trivial
      · exact reads_namesFit 0 _ _ (by positivity) operand copied)
    (by
      intro value before represented operand member
      have size := represented_size _ represented
      rw [layout.input_words, statePrefix_words] at size
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact layout.input.representation.fits
      simp only [rejectOperands, List.mem_append, List.mem_singleton] at member
      rcases member with ((literal | copied) | rfl) | copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
      · exact reads_valid 1 0 _ _ before (by decide) (by unfold stateOffset; omega) fits operand copied
      · trivial
      · exact reads_valid 1 0 _ _ before (by decide) (by unfold stateOffset; omega) fits operand copied)
    (by
      intro value before represented
      let leading := layout.hash.scheme.message.representation.encoding.encode (inputMessage layout value) ++
        layout.points.representation.encoding.encode (inputPoints layout value) ++
          layout.coefficients.representation.encoding.encode (inputRows layout value)
      have leadingLength : leading.length = stateOffset layout := by
        simp only [leading, stateOffset, List.length_append, Encoding.encode_length]
      have contents : (before.bufs 0).toList = leading ++ (statePrefix layout (inputState layout value) ++
          [if value.val.2.2.2.2.2.2.1 then 1 else 0, if value.val.2.2.2.2.2.2.2 then 1 else 0]) := by
        have bytes := represented.2.1
        rw [input_bytes, statePrefix_bytes] at bytes
        simp only [leading, List.append_assoc, inputState] at bytes ⊢
        exact bytes
      have history := ListFold.reads_block leading (statePrefix layout (inputState layout value))
        [if value.val.2.2.2.2.2.2.1 then 1 else 0, if value.val.2.2.2.2.2.2.2 then 1 else 0] before
        (by simpa only [List.append_assoc] using contents)
      have bad := ListFold.reads_block
        (leading ++ statePrefix layout (inputState layout value) ++ [if value.val.2.2.2.2.2.2.1 then 1 else 0])
        [if value.val.2.2.2.2.2.2.2 then 1 else 0] [] before (by
          simpa only [List.append_assoc, List.append_nil, List.singleton_append] using contents)
      simp only [List.length_append, List.length_cons, List.length_nil, leadingLength, statePrefix_length] at history bad
      rw [reject_bytes]
      simp only [rejectOperands, values, List.map_append, List.map_map]
      change _ ++ values (reads 0 _ _) before ++ [1] ++ values (reads 0 _ _) before = _
      rw [history, bad]
      exact congrArg (fun bytes => ((bytes ++ _) ++ [1]) ++ _) (List.map_id _))

theorem reject_time (value : layout.input.Value) :
    (reject layout zeroValid).time value ≤ 8 * (Read.output layout.hash.scheme).representation.encoding.words := by
  have bound := code_time_unit_le (rejectOperands layout zeroValid)
  rw [rejectOperands_length] at bound
  exact bound
theorem reject_words : descriptionWords (reject layout zeroValid).code ≤
    26 * (Read.output layout.hash.scheme).representation.encoding.words + 14 := by
  have bound := code_descriptionWords_le (rejectOperands layout zeroValid)
  rw [rejectOperands_length] at bound
  exact bound
theorem reject_names (slots : Nat) : NamesAccounted (reject layout zeroValid).code slots :=
  code_namesAccounted _ _ (rejectOperands_sources layout zeroValid)
theorem reject_buffers : (reject layout zeroValid).code.memBound ≤ 2 :=
  (code_names _ _ (rejectOperands_sources layout zeroValid)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.HashDispatch
