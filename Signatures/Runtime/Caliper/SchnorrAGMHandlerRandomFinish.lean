import Signatures.Runtime.Caliper.SchnorrAGMHandlerRandomPrepare

/-! Restore the common store after randomness handling. The saved configuration
is copied back between the reply and the updated mutable state. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent
open Caliper BoundedSource Assembly
variable {w qH qS randomBound : Nat} {M F G : Type}
  (layout : Handler.Layouts w M F G qH qS randomBound)

def resultReply (args : layout.random.output.Value × layout.scheme.config.Value) : layout.random.reply.Value :=
  ⟨args.1.val.1, args.1.property.1⟩
def resultState (args : layout.random.output.Value × layout.scheme.config.Value) : layout.scheme.state.Value :=
  ⟨args.1.val.2, args.1.property.2⟩
def finishValue (args : layout.random.output.Value × layout.scheme.config.Value) : layout.randomOutput.Value :=
  ⟨(args.1.val.1, args.2.val, args.1.val.2), args.1.property.1, args.2.property, args.1.property.2⟩
theorem finished_bytes (args : layout.random.output.Value × layout.scheme.config.Value) :
    (finished layout).encoding.encode args =
      (layout.random.reply.representation.encoding.encode (resultReply layout args) ++
        layout.scheme.state.representation.encoding.encode (resultState layout args)) ++
        layout.scheme.config.representation.encoding.encode args.2 := rfl
theorem output_bytes (args : layout.random.output.Value × layout.scheme.config.Value) :
    layout.randomOutput.representation.encoding.encode (finishValue layout args) =
      layout.random.reply.representation.encoding.encode (resultReply layout args) ++
        (layout.scheme.config.representation.encoding.encode args.2 ++
          layout.scheme.state.representation.encoding.encode (resultState layout args)) := rfl

def finishOperands : List (Operand w) :=
  reads 0 0 layout.random.reply.representation.encoding.words ++
    reads 0 (layout.random.reply.representation.encoding.words + layout.scheme.state.representation.encoding.words)
      layout.scheme.config.representation.encoding.words ++
    reads 0 layout.random.reply.representation.encoding.words layout.scheme.state.representation.encoding.words
theorem finishOperands_length : (finishOperands layout).length = layout.randomOutput.representation.encoding.words := by
  simp only [finishOperands, List.length_append, reads_length]
  change _ = layout.random.reply.representation.encoding.words +
    (layout.scheme.config.representation.encoding.words + layout.scheme.state.representation.encoding.words)
  omega
theorem finishOperands_sources : SourcesBound (finishOperands layout) 1 := by
  simp only [finishOperands, sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩
theorem finishOperands_names : ∀ operand ∈ finishOperands layout, operand.NamesFit := by
  intro operand member
  simp only [finishOperands, List.mem_append] at member
  rcases member with (member | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

def finish : Realizer .unit (finished layout) layout.randomOutput.representation (finishValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (finishOperands layout) layout.scheme.wordFits
    (finishOperands_length layout) (finishOperands_names layout)
    (by
      intro args before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = (layout.random.reply.representation.encoding.words +
        layout.scheme.state.representation.encoding.words) + layout.scheme.config.representation.encoding.words at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact (finished layout).fits
      simp only [finishOperands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro args before represented
      have contents := represented.2.1
      rw [finished_bytes] at contents
      let reply := layout.random.reply.representation.encoding.encode (resultReply layout args)
      let state := layout.scheme.state.representation.encoding.encode (resultState layout args)
      let config := layout.scheme.config.representation.encoding.encode args.2
      have readReply := ListFold.reads_block [] reply (state ++ config) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have readState := ListFold.reads_block reply state config before contents
      have readConfig := ListFold.reads_block (reply ++ state) config [] before
        (by simpa only [List.append_nil] using contents)
      have replyLength : reply.length = layout.random.reply.representation.encoding.words := Encoding.encode_length _ _
      have stateLength : state.length = layout.scheme.state.representation.encoding.words := Encoding.encode_length _ _
      have configLength : config.length = layout.scheme.config.representation.encoding.words := Encoding.encode_length _ _
      simp only [List.length_append, List.length_nil, replyLength, stateLength, configLength] at readReply readState readConfig
      rw [output_bytes]
      simp only [finishOperands, values, List.map_append]
      change (values (reads 0 0 _) before ++ values (reads 0 (_ + _) _) before) ++ values (reads 0 _ _) before = _
      rw [readReply, readConfig, readState]
      exact List.append_assoc _ _ _)

theorem finish_time (args : layout.random.output.Value × layout.scheme.config.Value) :
    (finish layout).time args ≤ 8 * layout.randomOutput.representation.encoding.words := by
  have bound := code_time_unit_le (finishOperands layout)
  rw [finishOperands_length] at bound
  exact bound
theorem finish_words : descriptionWords (finish layout).code ≤ 26 * layout.randomOutput.representation.encoding.words + 14 := by
  have bound := code_descriptionWords_le (finishOperands layout)
  rw [finishOperands_length] at bound
  exact bound
theorem finish_names (slots : Nat) : NamesAccounted (finish layout).code slots :=
  code_namesAccounted _ _ (finishOperands_sources layout)
theorem finish_buffers : (finish layout).code.memBound ≤ 2 :=
  (code_names _ _ (finishOperands_sources layout)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent
