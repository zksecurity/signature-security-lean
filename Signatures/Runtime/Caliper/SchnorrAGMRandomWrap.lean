import Signatures.Runtime.Caliper.SchnorrAGMRandomPrepare

/-! Random replies copy the sampled index and retained state, inserting the
encoded empty group list. The original range word is consumed explicitly. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
open Caliper BoundedSource Assembly
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)

def emptyGroups : layout.replyPoints.Value :=
  ⟨[], by simp only [List.length_nil, Nat.zero_le], by change ∀ point ∈ [], layout.scheme.point.valid point; simp⟩
def wrapValue (args : UniformQuery.Reply randomBound × layout.scheme.state.Value) : layout.output.Value :=
  ⟨((args.1.2.val, []), args.2.val), ⟨by
    change args.1.2.val < randomBound + 1
    have := args.1.2.isLt
    have := args.1.1.isLt
    omega, (emptyGroups layout).property⟩, args.2.property⟩
theorem wrap_bytes (args : UniformQuery.Reply randomBound × layout.scheme.state.Value) :
    layout.output.representation.encoding.encode (wrapValue layout args) =
      ([BitVec.ofNat w args.1.2.val] ++ layout.replyPoints.representation.encoding.encode (emptyGroups layout)) ++
        layout.scheme.state.representation.encoding.encode args.2 := rfl
theorem forwarded_bytes (args : UniformQuery.Reply randomBound × layout.scheme.state.Value) :
    layout.forwarded.encoding.encode args = [BitVec.ofNat w args.1.1.val, BitVec.ofNat w args.1.2.val] ++
      layout.scheme.state.representation.encoding.encode args.2 := rfl

def wrapOperands : List (Operand w) := reads 0 1 1 ++
  (layout.replyPoints.representation.encoding.encode (emptyGroups layout)).map Operand.literal ++
    reads 0 2 layout.scheme.state.representation.encoding.words
theorem wrapOperands_length : (wrapOperands layout).length = layout.output.representation.encoding.words := by
  simp only [wrapOperands, List.length_append, reads_length, List.length_map, Encoding.encode_length]
  rfl
theorem wrapOperands_sources : SourcesBound (wrapOperands layout) 1 := by
  simp only [wrapOperands, sourcesBound_append]
  refine ⟨⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial
def wrap : Realizer .unit layout.forwarded layout.output.representation (wrapValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (wrapOperands layout) layout.scheme.wordFits (wrapOperands_length layout)
    (by
      intro operand member
      simp only [wrapOperands, List.mem_append] at member
      rcases member with (copied | literal) | copied
      · exact reads_namesFit 0 _ _ (by positivity) operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
      · exact reads_namesFit 0 _ _ (by positivity) operand copied)
    (by
      intro args before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = 2 + layout.scheme.state.representation.encoding.words at size
      have fits : (before.bufs 0).size < 2 ^ w := by rw [represented_size _ represented]; exact layout.forwarded.fits
      simp only [wrapOperands, List.mem_append] at member
      rcases member with (copied | literal) | copied
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied)
    (by
      intro args before represented
      have contents := represented.2.1
      rw [forwarded_bytes] at contents
      have answer := ListFold.reads_block [BitVec.ofNat w args.1.1.val] [BitVec.ofNat w args.1.2.val]
        (layout.scheme.state.representation.encoding.encode args.2) before contents
      have state := ListFold.reads_block [BitVec.ofNat w args.1.1.val, BitVec.ofNat w args.1.2.val]
        (layout.scheme.state.representation.encoding.encode args.2) [] before (by simpa only [List.append_nil] using contents)
      simp only [List.length_cons, List.length_nil, Encoding.encode_length] at answer state
      rw [wrap_bytes]
      simp only [wrapOperands, values, List.map_append, List.map_map]
      change (values (reads 0 1 1) before ++ _) ++ values (reads 0 2 _) before = _
      rw [answer, state]
      exact congrArg (fun bytes => ([BitVec.ofNat w args.1.2.val] ++ bytes) ++ _) (List.map_id _))

theorem wrap_time (args : UniformQuery.Reply randomBound × layout.scheme.state.Value) :
    (wrap layout).time args ≤ 8 * layout.output.representation.encoding.words := by
  have bound := code_time_unit_le (wrapOperands layout)
  rw [wrapOperands_length] at bound
  exact bound
theorem wrap_words : descriptionWords (wrap layout).code ≤ 26 * layout.output.representation.encoding.words + 14 := by
  have bound := code_descriptionWords_le (wrapOperands layout)
  rw [wrapOperands_length] at bound
  exact bound
theorem wrap_names (slots : Nat) : NamesAccounted (wrap layout).code slots := code_namesAccounted _ _ (wrapOperands_sources layout)
theorem wrap_buffers : (wrap layout).code.memBound ≤ 2 := (code_names _ _ (wrapOperands_sources layout)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
