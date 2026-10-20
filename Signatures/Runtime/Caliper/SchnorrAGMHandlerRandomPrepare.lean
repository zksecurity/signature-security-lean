import Signatures.Runtime.Caliper.SchnorrAGMHandlerLayout
import Signatures.Runtime.Caliper.InteractiveRetain

/-! The common randomness input stores the generator and public key alongside
the mutable state. This preparation copies the core argument and moves the
configuration into an explicit suffix for `Interactive.retain`. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent
open Caliper BoundedSource Assembly
variable {w qH qS randomBound : Nat} {M F G : Type}
  (layout : Handler.Layouts w M F G qH qS randomBound)

theorem inputFits : layout.random.input.representation.encoding.words +
    layout.scheme.config.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by
    have := layout.random.input_le; have := layout.core_widths; have := layout.config_le; omega)
theorem outputFits : layout.random.output.representation.encoding.words +
    layout.scheme.config.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by
    have := layout.random.output_le; have := layout.core_widths; have := layout.config_le; omega)
def prepared := layout.random.input.representation.prod layout.scheme.config.representation (inputFits layout)
def finished := layout.random.output.representation.prod layout.scheme.config.representation (outputFits layout)

def requestLists (args : layout.randomInput.Value) : layout.lists.Value :=
  ⟨args.val.1.2, args.property.1.2⟩
def requestRange (args : layout.randomInput.Value) : layout.random.counter.Value :=
  ⟨args.val.1.1, args.property.1.1⟩
def requestConfig (args : layout.randomInput.Value) : layout.scheme.config.Value :=
  ⟨args.val.2.1, args.property.2.1⟩
def requestState (args : layout.randomInput.Value) : layout.scheme.state.Value :=
  ⟨args.val.2.2, args.property.2.2⟩
def prepareValue (args : layout.randomInput.Value) : layout.random.input.Value × layout.scheme.config.Value :=
  (⟨(args.val.1.2.1, args.val.1.2.2, args.val.1.1, args.val.2.2),
    args.property.1.2.1, args.property.1.2.2, args.property.1.1, args.property.2.2⟩,
    requestConfig layout args)

theorem input_bytes (args : layout.randomInput.Value) :
    layout.randomInput.representation.encoding.encode args =
      ((layout.random.counter.representation.encoding.encode (requestRange layout args) ++
        layout.lists.representation.encoding.encode (requestLists layout args)) ++
        layout.scheme.config.representation.encoding.encode (requestConfig layout args)) ++
        layout.scheme.state.representation.encoding.encode (requestState layout args) := by
  change (_ ++ _) ++ (_ ++ _) = _
  simp only [List.append_assoc]
  rfl
theorem prepared_bytes (args : layout.randomInput.Value) :
    (prepared layout).encoding.encode (prepareValue layout args) =
      ((layout.lists.representation.encoding.encode (requestLists layout args) ++
        layout.random.counter.representation.encoding.encode (requestRange layout args)) ++
        layout.scheme.state.representation.encoding.encode (requestState layout args)) ++
        layout.scheme.config.representation.encoding.encode (requestConfig layout args) := by
  change (_ ++ (_ ++ (_ ++ _))) ++ _ = (((_ ++ _) ++ _) ++ _) ++ _
  simp only [List.append_assoc]
  rfl

def prepareOperands : List (Operand w) :=
  reads 0 1 layout.lists.representation.encoding.words ++ reads 0 0 1 ++
    reads 0 (1 + layout.lists.representation.encoding.words + layout.scheme.config.representation.encoding.words)
      layout.scheme.state.representation.encoding.words ++
    reads 0 (1 + layout.lists.representation.encoding.words) layout.scheme.config.representation.encoding.words
theorem prepareOperands_length : (prepareOperands layout).length = (prepared layout).encoding.words := by
  simp only [prepareOperands, List.length_append, reads_length]
  change _ = (layout.random.points.representation.encoding.words +
    (layout.random.coefficientRows.representation.encoding.words +
      (1 + layout.scheme.state.representation.encoding.words))) + layout.scheme.config.representation.encoding.words
  rw [Handler.Layouts.lists_words]
  dsimp only [Handler.Layouts.points, Handler.Layouts.coefficientRows]
  omega
theorem prepareOperands_sources : SourcesBound (prepareOperands layout) 1 := by
  simp only [prepareOperands, sourcesBound_append]
  exact ⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩
theorem prepareOperands_names : ∀ operand ∈ prepareOperands layout, operand.NamesFit := by
  intro operand member
  simp only [prepareOperands, List.mem_append] at member
  rcases member with ((member | member) | member) | member <;>
    exact reads_namesFit 0 _ _ (by positivity) operand member

def prepare : Realizer .unit layout.randomInput.representation (prepared layout) (prepareValue layout) :=
  Assembly.realizer .unit (by decide) _ _ _ (prepareOperands layout) layout.scheme.wordFits
    (prepareOperands_length layout) (prepareOperands_names layout)
    (by
      intro args before represented operand member
      have size := represented_size _ represented
      change (before.bufs 0).size = (1 + layout.lists.representation.encoding.words) +
        (layout.scheme.config.representation.encoding.words + layout.scheme.state.representation.encoding.words) at size
      have fits : (before.bufs 0).size < 2 ^ w := by
        rw [represented_size _ represented]; exact layout.randomInput.representation.fits
      simp only [prepareOperands, List.mem_append] at member
      rcases member with ((member | member) | member) | member <;>
        exact reads_valid 1 0 _ _ before (by decide) (by omega) fits operand member)
    (by
      intro args before represented
      have contents := represented.2.1
      rw [input_bytes] at contents
      let n := layout.random.counter.representation.encoding.encode (requestRange layout args)
      let lists := layout.lists.representation.encoding.encode (requestLists layout args)
      let config := layout.scheme.config.representation.encoding.encode (requestConfig layout args)
      let state := layout.scheme.state.representation.encoding.encode (requestState layout args)
      have readLists := ListFold.reads_block n lists (config ++ state) before
        (by simpa only [List.append_assoc] using contents)
      have readRange := ListFold.reads_block [] n (lists ++ config ++ state) before
        (by simpa only [List.nil_append, List.append_assoc] using contents)
      have readConfig := ListFold.reads_block (n ++ lists) config state before contents
      have readState := ListFold.reads_block (n ++ lists ++ config) state [] before
        (by simpa only [List.append_nil] using contents)
      have nLength : n.length = 1 := layout.random.counter.representation.encoding.encode_length _
      have listsLength : lists.length = layout.lists.representation.encoding.words := Encoding.encode_length _ _
      have configLength : config.length = layout.scheme.config.representation.encoding.words := Encoding.encode_length _ _
      have stateLength : state.length = layout.scheme.state.representation.encoding.words := Encoding.encode_length _ _
      simp only [List.length_append, List.length_nil, nLength, listsLength, configLength, stateLength] at readLists readRange readConfig readState
      rw [prepared_bytes]
      simp only [prepareOperands, values, List.map_append]
      change ((values (reads 0 1 _) before ++ values (reads 0 0 1) before) ++
        values (reads 0 (1 + _ + _) _) before) ++ values (reads 0 (1 + _) _) before = _
      rw [readLists, readRange, readState, readConfig])

theorem prepare_time (args : layout.randomInput.Value) :
    (prepare layout).time args ≤ 8 * (prepared layout).encoding.words := by
  have bound := code_time_unit_le (prepareOperands layout)
  rw [prepareOperands_length] at bound
  exact bound
theorem prepare_words : descriptionWords (prepare layout).code ≤ 26 * (prepared layout).encoding.words + 14 := by
  have bound := code_descriptionWords_le (prepareOperands layout)
  rw [prepareOperands_length] at bound
  exact bound
theorem prepare_names (slots : Nat) : NamesAccounted (prepare layout).code slots :=
  code_namesAccounted _ _ (prepareOperands_sources layout)
theorem prepare_buffers : (prepare layout).code.memBound ≤ 2 :=
  (code_names _ _ (prepareOperands_sources layout)).2

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent
