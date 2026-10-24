import Proofs.Runtime.Caliper.SchnorrAGMRandom
import Proofs.Runtime.Caliper.InteractiveMemory

/-! Bounds charge the request test, marking, all stored branch code, the
dynamic query, retained state and empty-group reply assembly. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
open Caliper BoundedSource OracleComp OracleSpec
private theorem composed_words {w : Nat} {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (preparation wrapping : Stmt w) (queryCode : Interactive.Code w) :
    ((Interactive.Code.seq (.compute preparation) (.seq queryCode (.compute wrapping))).lower port).descriptionWords =
      descriptionWords preparation + (queryCode.lower port).descriptionWords + descriptionWords wrapping + 4 := by
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega

variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)

def timeBudget : Nat := 160 * layout.width + 200
def codeBudget : Nat := 640 * layout.width + 800
theorem time_bound : Interactive.TimeBound layout.port .unit layout.input.representation (code layout) (timeBudget layout) := by
  have prepared := Interactive.TimeBound.compute (port := layout.port) (cost := .unit) (prepareQuery layout)
    (128 * layout.width + 128) (prepare_bounded layout).time_le
  have forwarded := UniformQuery.forward_time randomBound layout.scheme.wordFits layout.rangeFits
    layout.scheme.state.representation layout.frameFits
  have wrapped := Interactive.TimeBound.compute (port := layout.port) (cost := .unit) (wrap layout) _ (wrap_time layout)
  have combined := prepared.seq (Interactive.Refines.compute layout.port .unit (prepareQuery layout))
    (forwarded.seq (UniformQuery.forward_refines randomBound layout.scheme.wordFits layout.rangeFits
      layout.scheme.state.representation layout.frameFits) wrapped)
  apply combined.mono
  have state := layout.state_le
  have parts := layout.parts
  have output := layout.output_le
  unfold timeBudget
  omega
theorem code_bound : ((code layout).lower layout.port).descriptionWords ≤ codeBudget layout := by
  have prepared := (prepare_bounded layout).code_le
  have forwarded := UniformQuery.forward_words randomBound layout.scheme.wordFits layout.rangeFits layout.scheme.state.representation
  have wrapped := wrap_words layout
  change ((forward layout).lower layout.port).descriptionWords ≤ _ at forwarded
  have form := composed_words layout.port (prepareQuery layout).code (wrap layout).code (forward layout)
  change ((code layout).lower layout.port).descriptionWords = descriptionWords (prepare layout).program.code +
    ((forward layout).lower layout.port).descriptionWords + descriptionWords (wrap layout).code + 4 at form
  rw [form]
  have state := layout.state_le
  have parts := layout.parts
  have output := layout.output_le
  unfold codeBudget
  omega
theorem names : WordIO.NamesAccounted ((code layout).lower layout.port) 5 :=
  (WordIO.NamesAccounted.compute (prepare_names layout)).seq
    (((UniformQuery.forward_names randomBound layout.scheme.wordFits layout.rangeFits layout.scheme.state.representation).accounted.mono (by decide)).seq
      (WordIO.NamesAccounted.compute (wrap_names layout 5)))
theorem buffers : ((code layout).lower layout.port).memBound ≤ 6 :=
  max_le (prepare_buffers layout)
    (max_le ((UniformQuery.forward_names randomBound layout.scheme.wordFits layout.rangeFits layout.scheme.state.representation).buffers.trans (by decide))
      ((wrap_buffers layout).trans (by decide)))
theorem descriptionFits : ((code layout).lower layout.port).DescriptionFits :=
  .seq layout.scheme.wordFits (.compute (prepareQuery layout).description_fits)
    (.seq layout.scheme.wordFits
      (UniformQuery.forward_descriptionFits randomBound layout.scheme.wordFits layout.rangeFits layout.scheme.state.representation layout.frameFits)
      (.compute (wrap layout).description_fits))

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Random
