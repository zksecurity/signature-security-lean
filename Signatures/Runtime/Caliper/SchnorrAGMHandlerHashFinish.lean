import Signatures.Runtime.Caliper.SchnorrAGMHandlerHashPrepare

/-! Restore the runtime configuration and construct the hash reply's empty
group list with actual literal/copy instructions, including its padding. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
open Caliper BoundedSource Assembly
variable {w qH qS randomBound : Nat} {M F G : Type}
  (layout : Handler.Layouts w M F G qH qS randomBound)

def emptyGroups : layout.signing.replyPoints.Value :=
  ⟨[], by simp only [List.length_nil, Nat.zero_le], by change ∀ point ∈ [], layout.scheme.point.valid point; simp⟩
def resultScalar (args : (Read.output layout.scheme).Value × layout.scheme.config.Value) : layout.scheme.scalar.Value :=
  ⟨args.1.val.1, args.1.property.1⟩
def resultState (args : (Read.output layout.scheme).Value × layout.scheme.config.Value) : layout.scheme.state.Value :=
  ⟨args.1.val.2, args.1.property.2⟩
def finishValue (args : (Read.output layout.scheme).Value × layout.scheme.config.Value) : layout.scalarOutput.Value :=
  ⟨((args.1.val.1, []), args.2.val, args.1.val.2),
    ⟨args.1.property.1, (emptyGroups layout).property⟩, args.2.property, args.1.property.2⟩
theorem finished_bytes (args : (Read.output layout.scheme).Value × layout.scheme.config.Value) :
    layout.hashFinished.encoding.encode args =
      (layout.scheme.scalar.representation.encoding.encode (resultScalar layout args) ++
        layout.scheme.state.representation.encoding.encode (resultState layout args)) ++
        layout.scheme.config.representation.encoding.encode args.2 := rfl
theorem output_bytes (args : (Read.output layout.scheme).Value × layout.scheme.config.Value) :
    layout.scalarOutput.representation.encoding.encode (finishValue layout args) =
      (layout.scheme.scalar.representation.encoding.encode (resultScalar layout args) ++
        layout.signing.replyPoints.representation.encoding.encode (emptyGroups layout)) ++
        (layout.scheme.config.representation.encoding.encode args.2 ++
          layout.scheme.state.representation.encoding.encode (resultState layout args)) := rfl

def finishOperands : List (Operand w) :=
  reads 0 0 layout.scheme.scalar.representation.encoding.words ++
    (layout.signing.replyPoints.representation.encoding.encode (emptyGroups layout)).map Operand.literal ++
    reads 0 (layout.scheme.scalar.representation.encoding.words + layout.scheme.state.representation.encoding.words)
      layout.scheme.config.representation.encoding.words ++
    reads 0 layout.scheme.scalar.representation.encoding.words layout.scheme.state.representation.encoding.words
theorem finishOperands_length : (finishOperands layout).length = layout.scalarOutput.representation.encoding.words := by
  simp only [finishOperands, List.length_append, reads_length, List.length_map, Encoding.encode_length]
  change _ = (layout.scheme.scalar.representation.encoding.words + layout.signing.replyPoints.representation.encoding.words) +
    (layout.scheme.config.representation.encoding.words + layout.scheme.state.representation.encoding.words)
  omega
theorem finishOperands_sources : SourcesBound (finishOperands layout) 1 := by
  simp only [finishOperands, sourcesBound_append]
  refine ⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), ?_⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩
  intro operand member
  obtain ⟨word, _, rfl⟩ := List.mem_map.mp member
  trivial
theorem finishOperands_names : ∀ operand ∈ finishOperands layout, operand.NamesFit := by
  intro operand member
  simp only [finishOperands, List.mem_append] at member
  rcases member with ((copied | literal) | copied) | copied
  · exact reads_namesFit 0 _ _ (by positivity) operand copied
  · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
  · exact reads_namesFit 0 _ _ (by positivity) operand copied
  · exact reads_namesFit 0 _ _ (by positivity) operand copied

def finish : Realizer .unit layout.hashFinished layout.scalarOutput.representation (finishValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (finishOperands layout) layout.scheme.wordFits
    (finishOperands_length layout) (finishOperands_names layout)
    (by
      intro args before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = (layout.scheme.scalar.representation.encoding.words +
        layout.scheme.state.representation.encoding.words) + layout.scheme.config.representation.encoding.words at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact layout.hashFinished.fits
      simp only [finishOperands, List.mem_append] at member
      rcases member with ((copied | literal) | copied) | copied
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp literal; trivial
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied
      · exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand copied)
    (by
      intro args before represented
      have contents := represented.2.1
      rw [finished_bytes] at contents
      let scalar := layout.scheme.scalar.representation.encoding.encode (resultScalar layout args)
      let state := layout.scheme.state.representation.encoding.encode (resultState layout args)
      let config := layout.scheme.config.representation.encoding.encode args.2
      have readScalar := ListFold.reads_block [] scalar (state ++ config) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have readState := ListFold.reads_block scalar state config before contents
      have readConfig := ListFold.reads_block (scalar ++ state) config [] before
        (by simpa only [List.append_nil] using contents)
      have scalarLength : scalar.length = layout.scheme.scalar.representation.encoding.words := Encoding.encode_length _ _
      have stateLength : state.length = layout.scheme.state.representation.encoding.words := Encoding.encode_length _ _
      have configLength : config.length = layout.scheme.config.representation.encoding.words := Encoding.encode_length _ _
      simp only [List.length_append, List.length_nil, scalarLength, stateLength, configLength] at readScalar readState readConfig
      rw [output_bytes]
      simp only [finishOperands, values, List.map_append, List.map_map]
      change ((values (reads 0 0 _) before ++ _) ++ values (reads 0 (_ + _) _) before) ++ values (reads 0 _ _) before = _
      rw [readScalar, readConfig, readState]
      simp only [List.append_assoc]
      exact congrArg (fun bytes => scalar ++ (bytes ++ (config ++ state))) (List.map_id _))

theorem finish_time (args : (Read.output layout.scheme).Value × layout.scheme.config.Value) :
    (finish layout).time args ≤ 8 * layout.scalarOutput.representation.encoding.words := by
  have bound := code_time_unit_le (finishOperands layout)
  rw [finishOperands_length] at bound
  exact bound
theorem finish_words : descriptionWords (finish layout).code ≤ 26 * layout.scalarOutput.representation.encoding.words + 14 := by
  have bound := code_descriptionWords_le (finishOperands layout)
  rw [finishOperands_length] at bound
  exact bound
theorem finish_names (slots : Nat) : NamesAccounted (finish layout).code slots :=
  code_namesAccounted _ _ (finishOperands_sources layout)
theorem finish_buffers : (finish layout).code.memBound ≤ 2 :=
  (code_names _ _ (finishOperands_sources layout)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
