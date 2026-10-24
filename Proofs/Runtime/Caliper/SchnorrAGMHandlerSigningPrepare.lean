import Proofs.Runtime.Caliper.SchnorrAGMHandlerGroupLayout
import Proofs.Runtime.Caliper.InteractiveRetain

/-! Signing uses the generator/public key in its argument and retains a second
copy for the common store. Both copies are made by actual word instructions. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
open Caliper BoundedSource Assembly
variable {w qH qS randomBound : Nat} {M F G : Type}
  (layout : Handler.Layouts w M F G qH qS randomBound)

def requestMessage (args : layout.signingInput.Value) : layout.scheme.message.Value :=
  ⟨args.val.1.1, args.property.1.1.1⟩
def requestLists (args : layout.signingInput.Value) : layout.lists.Value :=
  ⟨args.val.1.2, args.property.1.1.2⟩
def requestConfig (args : layout.signingInput.Value) : layout.scheme.config.Value :=
  ⟨args.val.2.1, args.property.1.2.1⟩
def requestState (args : layout.signingInput.Value) : layout.scheme.state.Value :=
  ⟨args.val.2.2, args.property.1.2.2⟩
def prepareValue (args : layout.signingInput.Value) : layout.signing.input.Value × layout.scheme.config.Value :=
  (layout.signingValue args, requestConfig layout args)

theorem input_bytes (args : layout.signingInput.Value) :
    layout.signingInput.representation.encoding.encode args =
      (layout.scheme.message.representation.encoding.encode (requestMessage layout args) ++
        layout.lists.representation.encoding.encode (requestLists layout args)) ++
        (layout.scheme.config.representation.encoding.encode (requestConfig layout args) ++
          layout.scheme.state.representation.encoding.encode (requestState layout args)) := rfl
theorem prepared_bytes (args : layout.signingInput.Value) :
    layout.signingPrepared.encoding.encode (prepareValue layout args) =
      (((layout.lists.representation.encoding.encode (requestLists layout args) ++
        layout.scheme.config.representation.encoding.encode (requestConfig layout args)) ++
        layout.scheme.message.representation.encoding.encode (requestMessage layout args)) ++
        layout.scheme.state.representation.encoding.encode (requestState layout args)) ++
        layout.scheme.config.representation.encoding.encode (requestConfig layout args) := by
  change (_ ++ (_ ++ (_ ++ (_ ++ (_ ++ _))))) ++ _ = ((((_ ++ _) ++ (_ ++ _)) ++ _) ++ _) ++ _
  simp only [List.append_assoc]
  rfl

def prepareOperands : List (Operand w) :=
  reads 0 layout.scheme.message.representation.encoding.words
    (layout.lists.representation.encoding.words + layout.scheme.config.representation.encoding.words) ++
    reads 0 0 layout.scheme.message.representation.encoding.words ++
    reads 0 (layout.scheme.message.representation.encoding.words + layout.lists.representation.encoding.words +
      layout.scheme.config.representation.encoding.words) layout.scheme.state.representation.encoding.words ++
    reads 0 (layout.scheme.message.representation.encoding.words + layout.lists.representation.encoding.words)
      layout.scheme.config.representation.encoding.words
theorem prepareOperands_length : (prepareOperands layout).length = layout.signingPrepared.encoding.words := by
  simp only [prepareOperands, List.length_append, reads_length]
  change _ = layout.signing.input.representation.encoding.words + layout.scheme.config.representation.encoding.words
  rw [layout.signing_input_words]
theorem prepareOperands_sources : SourcesBound (prepareOperands layout) 1 := by
  simp only [prepareOperands, sourcesBound_append]
  exact ⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
theorem prepareOperands_names : ∀ operand ∈ prepareOperands layout, operand.NamesFit := by
  intro operand member
  simp only [prepareOperands, List.mem_append] at member
  rcases member with ((member | member) | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

def prepare : Realizer .unit layout.signingInput.representation layout.signingPrepared (prepareValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (prepareOperands layout) layout.scheme.wordFits
    (prepareOperands_length layout) (prepareOperands_names layout)
    (by
      intro args before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = (layout.scheme.message.representation.encoding.words + layout.lists.representation.encoding.words) +
        (layout.scheme.config.representation.encoding.words + layout.scheme.state.representation.encoding.words) at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact layout.signingInput.representation.fits
      simp only [prepareOperands, List.mem_append] at member
      rcases member with ((member | member) | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro args before represented
      have contents := represented.2.1
      rw [input_bytes] at contents
      let message := layout.scheme.message.representation.encoding.encode (requestMessage layout args)
      let lists := layout.lists.representation.encoding.encode (requestLists layout args)
      let config := layout.scheme.config.representation.encoding.encode (requestConfig layout args)
      let state := layout.scheme.state.representation.encoding.encode (requestState layout args)
      have readListsConfig := ListFold.reads_block message (lists ++ config) state before
        (by simpa only [List.append_assoc] using contents)
      have readMessage := ListFold.reads_block [] message (lists ++ config ++ state) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have readConfig := ListFold.reads_block (message ++ lists) config state before
        (by simpa only [List.append_assoc] using contents)
      have readState := ListFold.reads_block (message ++ lists ++ config) state [] before
        (by simpa only [List.append_nil, List.append_assoc] using contents)
      have messageLength : message.length = layout.scheme.message.representation.encoding.words := Encoding.encode_length _ _
      have listsLength : lists.length = layout.lists.representation.encoding.words := Encoding.encode_length _ _
      have configLength : config.length = layout.scheme.config.representation.encoding.words := Encoding.encode_length _ _
      have stateLength : state.length = layout.scheme.state.representation.encoding.words := Encoding.encode_length _ _
      simp only [List.length_append, List.length_nil, messageLength, listsLength, configLength, stateLength] at readListsConfig readMessage readConfig readState
      rw [prepared_bytes]
      simp only [prepareOperands, values, List.map_append]
      change ((values (reads 0 _ (_ + _)) before ++ values (reads 0 0 _) before) ++
        values (reads 0 (_ + _ + _) _) before) ++ values (reads 0 (_ + _) _) before = _
      rw [readListsConfig, readMessage, readState, readConfig])

theorem prepare_time (args : layout.signingInput.Value) :
    (prepare layout).time args ≤ 8 * layout.signingPrepared.encoding.words := by
  have bound := code_time_unit_le (prepareOperands layout)
  rw [prepareOperands_length] at bound
  exact bound
theorem prepare_words : descriptionWords (prepare layout).code ≤ 26 * layout.signingPrepared.encoding.words + 14 := by
  have bound := code_descriptionWords_le (prepareOperands layout)
  rw [prepareOperands_length] at bound
  exact bound
theorem prepare_names (slots : Nat) : NamesAccounted (prepare layout).code slots :=
  code_namesAccounted _ _ (prepareOperands_sources layout)
theorem prepare_buffers : (prepare layout).code.memBound ≤ 2 :=
  (code_names _ _ (prepareOperands_sources layout)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.SigningComponent
