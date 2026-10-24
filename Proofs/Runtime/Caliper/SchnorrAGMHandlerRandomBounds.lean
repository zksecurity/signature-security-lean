import Proofs.Runtime.Caliper.SchnorrAGMHandlerRandom

/-! Bounds include argument routing and the saved generator/public key, as well
as the randomness core. The saved buffer is derived from the core footprint. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent
open Caliper BoundedSource OracleComp OracleSpec
private theorem composed_words {w : Nat} {I : Type} {spec : OracleSpec I} (port : Interactive.Port w spec)
    (preparation wrapping : Stmt w) (body : Interactive.Code w) :
    ((Interactive.Code.seq (.compute preparation) (.seq body (.compute wrapping))).lower port).descriptionWords =
      descriptionWords preparation + (body.lower port).descriptionWords + descriptionWords wrapping + 4 := by
  simp only [Interactive.Code.lower, WordIO.Code.descriptionWords_seq, WordIO.Code.descriptionWords_compute]
  omega
variable {w qH qS randomBound : Nat} {M F G : Type}
  (layout : Handler.Layouts w M F G qH qS randomBound)

theorem widths : (prepared layout).encoding.words ≤ 2 * layout.width ∧
    layout.randomOutput.representation.encoding.words ≤ 2 * layout.width := by
  have input := layout.random.input_le
  have output := layout.random.output_le
  change layout.random.reply.representation.encoding.words + layout.random.scheme.state.representation.encoding.words ≤ _ at output
  have core := layout.core_widths
  have config := layout.config_le
  change (layout.random.input.representation.encoding.words + layout.scheme.config.representation.encoding.words ≤ _) ∧
    (layout.random.reply.representation.encoding.words +
      (layout.scheme.config.representation.encoding.words + layout.scheme.state.representation.encoding.words) ≤ _)
  change layout.random.reply.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤ _ at output
  omega

def timeBudget : Nat := 224 * layout.width + 200
def codeBudget : Nat := 864 * layout.width + 900
theorem retained_time : Interactive.TimeBound layout.random.port .unit (prepared layout) (retained layout)
    (SchnorrAGM.Random.timeBudget layout.random + 8 * layout.random.input.representation.encoding.words +
      8 * layout.random.output.representation.encoding.words + 12 * layout.scheme.config.representation.encoding.words) :=
  (Interactive.TimeBound.retain (SchnorrAGM.Random.refines layout.random) (SchnorrAGM.Random.time_bound layout.random)
    (by decide) layout.scheme.config.representation layout.scheme.wordFits (inputFits layout)).mono
      (Interactive.retain_time_unit_le _ _ _ _ _)
theorem time_bound : Interactive.TimeBound layout.random.port .unit layout.randomInput.representation
    (code layout) (timeBudget layout) := by
  have preparedBound := Interactive.TimeBound.compute (port := layout.random.port) (cost := .unit)
    (prepare layout) _ (prepare_time layout)
  have finishedBound := Interactive.TimeBound.compute (port := layout.random.port) (cost := .unit)
    (finish layout) _ (finish_time layout)
  have combined := preparedBound.seq (Interactive.Refines.compute layout.random.port .unit (prepare layout))
    ((retained_time layout).seq (retained_refines layout) finishedBound)
  apply combined.mono
  have := widths layout
  have := layout.random.input_le
  have := layout.random.output_le
  have := layout.core_widths
  have := layout.config_le
  unfold timeBudget SchnorrAGM.Random.timeBudget
  omega
theorem code_bound : ((code layout).lower layout.random.port).descriptionWords ≤ codeBudget layout := by
  have preparedBound := prepare_words layout
  have finishedBound := finish_words layout
  have coreBound := SchnorrAGM.Random.code_bound layout.random
  have retainedBound := Interactive.retain_descriptionWords_le layout.random.port (SchnorrAGM.Random.code layout.random)
    (Interactive.savedBuffer layout.random.port (SchnorrAGM.Random.code layout.random))
    layout.random.input.representation.encoding.words layout.random.output.representation.encoding.words
    layout.scheme.config.representation.encoding.words
  change ((retained layout).lower layout.random.port).descriptionWords ≤ _ at retainedBound
  have form := composed_words layout.random.port (prepare layout).code (finish layout).code (retained layout)
  change ((code layout).lower layout.random.port).descriptionWords = _ at form
  rw [form]
  have := widths layout
  have := layout.random.input_le
  have := layout.random.output_le
  have := layout.core_widths
  have := layout.config_le
  unfold codeBudget SchnorrAGM.Random.codeBudget at *
  omega
theorem names : WordIO.NamesAccounted ((code layout).lower layout.random.port) 5 :=
  (WordIO.NamesAccounted.compute (prepare_names layout 5)).seq
    ((Interactive.retain_names layout.random.port (SchnorrAGM.Random.names layout.random) _ _ _).seq
      (WordIO.NamesAccounted.compute (finish_names layout 5)))
theorem buffers : ((code layout).lower layout.random.port).memBound ≤ 7 := by
  have retainedBound := Interactive.retain_buffers layout.random.port (SchnorrAGM.Random.code layout.random)
    layout.random.input.representation.encoding.words layout.random.output.representation.encoding.words
    layout.scheme.config.representation.encoding.words
  have coreBound := SchnorrAGM.Random.buffers layout.random
  have retainedBound' : ((retained layout).lower layout.random.port).memBound ≤ 7 := retainedBound.trans (by omega)
  exact max_le ((prepare_buffers layout).trans (by decide))
    (max_le retainedBound' ((finish_buffers layout).trans (by decide)))
theorem descriptionFits : ((code layout).lower layout.random.port).DescriptionFits := by
  have name : Interactive.savedBuffer layout.random.port (SchnorrAGM.Random.code layout.random) < 2 ^ w := by
    have := SchnorrAGM.Random.buffers layout.random
    have := layout.scheme.wordFits
    unfold Interactive.savedBuffer
    omega
  have retainedFits := Interactive.retain_descriptionFits layout.random.port (SchnorrAGM.Random.code layout.random)
    (Interactive.savedBuffer layout.random.port (SchnorrAGM.Random.code layout.random))
    layout.random.input.representation.encoding.words layout.random.output.representation.encoding.words
    layout.scheme.config.representation.encoding.words layout.scheme.wordFits
    (SchnorrAGM.Random.descriptionFits layout.random) name layout.random.input.representation.fits
    layout.scheme.config.representation.fits (outputFits layout)
  exact .seq layout.scheme.wordFits (.compute (prepare layout).description_fits)
    (.seq layout.scheme.wordFits retainedFits (.compute (finish layout).description_fits))

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.RandomComponent
