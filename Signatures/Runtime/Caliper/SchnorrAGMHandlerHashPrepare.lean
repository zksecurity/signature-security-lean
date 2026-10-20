import Signatures.Runtime.Caliper.SchnorrAGMHandlerGroupLayout
import Signatures.Runtime.Caliper.InteractiveRetain

/-! Route the request and mutable state to the hash core, with the runtime
generator/public key in an explicit suffix for charged retention. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
open Caliper BoundedSource Assembly
variable {w qH qS randomBound : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
  (layout : Handler.Layouts w M F G qH qS randomBound)

def requestArgs (args : layout.hashInput.Value) : layout.groupArgs.Value :=
  ⟨args.val.1, args.property.1.1⟩
def requestConfig (args : layout.hashInput.Value) : layout.scheme.config.Value :=
  ⟨args.val.2.1, args.property.1.2.1⟩
def requestState (args : layout.hashInput.Value) : layout.scheme.state.Value :=
  ⟨args.val.2.2, args.property.1.2.2⟩
def prepareValue (args : layout.hashInput.Value) : layout.hash.input.Value × layout.scheme.config.Value :=
  (layout.hashValue args, requestConfig layout args)
theorem input_bytes (args : layout.hashInput.Value) :
    layout.hashInput.representation.encoding.encode args =
      layout.groupArgs.representation.encoding.encode (requestArgs layout args) ++
        (layout.scheme.config.representation.encoding.encode (requestConfig layout args) ++
          layout.scheme.state.representation.encoding.encode (requestState layout args)) := rfl
theorem prepared_bytes (args : layout.hashInput.Value) :
    layout.hashPrepared.encoding.encode (prepareValue layout args) =
      (layout.groupArgs.representation.encoding.encode (requestArgs layout args) ++
        layout.scheme.state.representation.encoding.encode (requestState layout args)) ++
        layout.scheme.config.representation.encoding.encode (requestConfig layout args) := by
  change (_ ++ (_ ++ (_ ++ _))) ++ _ = ((_ ++ (_ ++ _)) ++ _) ++ _
  simp only [List.append_assoc]
  rfl

def prepareOperands : List (Operand w) :=
  reads 0 0 layout.groupArgs.representation.encoding.words ++
    reads 0 (layout.groupArgs.representation.encoding.words + layout.scheme.config.representation.encoding.words)
      layout.scheme.state.representation.encoding.words ++
    reads 0 layout.groupArgs.representation.encoding.words layout.scheme.config.representation.encoding.words
theorem prepareOperands_length : (prepareOperands layout).length = layout.hashPrepared.encoding.words := by
  simp only [prepareOperands, List.length_append, reads_length]
  change _ = layout.hash.input.representation.encoding.words + layout.scheme.config.representation.encoding.words
  rw [layout.hash_input_words]
omit [DecidableEq M] [DecidableEq G] in
theorem prepareOperands_sources : SourcesBound (prepareOperands layout) 1 := by
  simp only [prepareOperands, sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩
omit [DecidableEq M] [DecidableEq G] in
theorem prepareOperands_names : ∀ operand ∈ prepareOperands layout, operand.NamesFit := by
  intro operand member
  simp only [prepareOperands, List.mem_append] at member
  rcases member with (member | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

def prepare : Realizer .unit layout.hashInput.representation layout.hashPrepared (prepareValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (prepareOperands layout) layout.scheme.wordFits
    (prepareOperands_length layout) (prepareOperands_names layout)
    (by
      intro args before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = layout.groupArgs.representation.encoding.words +
        (layout.scheme.config.representation.encoding.words + layout.scheme.state.representation.encoding.words) at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact layout.hashInput.representation.fits
      simp only [prepareOperands, List.mem_append] at member
      rcases member with (member | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro args before represented
      have contents := represented.2.1
      rw [input_bytes] at contents
      let request := layout.groupArgs.representation.encoding.encode (requestArgs layout args)
      let config := layout.scheme.config.representation.encoding.encode (requestConfig layout args)
      let state := layout.scheme.state.representation.encoding.encode (requestState layout args)
      have readArgs := ListFold.reads_block [] request (config ++ state) before
        (by simpa only [List.nil_append] using contents)
      have readConfig := ListFold.reads_block request config state before
        (by simpa only [List.append_assoc] using contents)
      have readState := ListFold.reads_block (request ++ config) state [] before
        (by simpa only [List.append_nil, List.append_assoc] using contents)
      have argsLength : request.length = layout.groupArgs.representation.encoding.words := Encoding.encode_length _ _
      have configLength : config.length = layout.scheme.config.representation.encoding.words := Encoding.encode_length _ _
      have stateLength : state.length = layout.scheme.state.representation.encoding.words := Encoding.encode_length _ _
      simp only [List.length_append, List.length_nil, argsLength, configLength, stateLength] at readArgs readConfig readState
      rw [prepared_bytes]
      simp only [prepareOperands, values, List.map_append]
      change (values (reads 0 0 _) before ++ values (reads 0 (_ + _) _) before) ++ values (reads 0 _ _) before = _
      rw [readArgs, readState, readConfig])

theorem prepare_time (args : layout.hashInput.Value) :
    (prepare layout).time args ≤ 8 * layout.hashPrepared.encoding.words := by
  have bound := code_time_unit_le (prepareOperands layout)
  rw [prepareOperands_length] at bound
  exact bound
theorem prepare_words : descriptionWords (prepare layout).code ≤ 26 * layout.hashPrepared.encoding.words + 14 := by
  have bound := code_descriptionWords_le (prepareOperands layout)
  rw [prepareOperands_length] at bound
  exact bound
theorem prepare_names (slots : Nat) : NamesAccounted (prepare layout).code slots :=
  code_namesAccounted _ _ (prepareOperands_sources layout)
theorem prepare_buffers : (prepare layout).code.memBound ≤ 2 :=
  (code_names _ _ (prepareOperands_sources layout)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.HashComponent
