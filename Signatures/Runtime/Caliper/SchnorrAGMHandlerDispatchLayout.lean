import Signatures.Runtime.Caliper.SchnorrAGMHandlerGroupLayout
import Signatures.Runtime.Caliper.InteractivePrefix
import Signatures.Runtime.Caliper.TagBounds

/-! Stored request/reply tags for the complete Schnorr service. Every returned
packet carries the entire original request, including supplied group lists and
coefficient rows. The component state is followed by this saved request. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.Dispatch
open Caliper BoundedSource
variable {w qH qS randomBound : Nat} {M F G : Type} [DecidableEq M] [DecidableEq G]
    (layout : Handler.Layouts w M F G qH qS randomBound)

def randomRequest (args : layout.randomInput.Value) : layout.randomArgs.Value :=
  ⟨args.val.1, args.property.1⟩
def hashRequest (args : layout.hashInput.Value) : layout.groupArgs.Value :=
  ⟨args.val.1, args.property.1.1⟩
def signingRequest (args : layout.signingInput.Value) : layout.groupArgs.Value :=
  ⟨args.val.1, args.property.1.1⟩

omit [DecidableEq M] [DecidableEq G] in
theorem random_prefix (args : layout.randomInput.Value) :
    (layout.randomInput.representation.encoding.encode args).take layout.randomArgs.representation.encoding.words =
      layout.randomArgs.representation.encoding.encode (randomRequest layout args) := by
  change (layout.randomArgs.representation.encoding.encode (randomRequest layout args) ++
    layout.scheme.store.representation.encoding.encode ⟨args.val.2, args.property.2⟩).take _ = _
  rw [← layout.randomArgs.representation.encoding.encode_length (randomRequest layout args), List.take_left]
theorem hash_prefix (args : layout.hashInput.Value) :
    (layout.hashInput.representation.encoding.encode args).take layout.groupArgs.representation.encoding.words =
      layout.groupArgs.representation.encoding.encode (hashRequest layout args) := by
  change (layout.groupArgs.representation.encoding.encode (hashRequest layout args) ++
    layout.scheme.store.representation.encoding.encode ⟨args.val.2, args.property.1.2⟩).take _ = _
  rw [← layout.groupArgs.representation.encoding.encode_length (hashRequest layout args), List.take_left]
omit [DecidableEq M] [DecidableEq G] in
theorem signing_prefix (args : layout.signingInput.Value) :
    (layout.signingInput.representation.encoding.encode args).take layout.groupArgs.representation.encoding.words =
      layout.groupArgs.representation.encoding.encode (signingRequest layout args) := by
  change (layout.groupArgs.representation.encoding.encode (signingRequest layout args) ++
    layout.scheme.store.representation.encoding.encode ⟨args.val.2, args.property.1.2⟩).take _ = _
  rw [← layout.groupArgs.representation.encoding.encode_length (signingRequest layout args), List.take_left]

theorem input_widths : layout.randomInput.representation.encoding.words ≤ 4 * layout.width ∧
    layout.hashInput.representation.encoding.words ≤ 4 * layout.width ∧
    layout.signingInput.representation.encoding.words ≤ 4 * layout.width := by
  have := layout.args_le; have := layout.store_le
  change _ + _ ≤ _ ∧ _ + _ ≤ _ ∧ _ + _ ≤ _
  omega
omit [DecidableEq M] [DecidableEq G] in
theorem random_output_le : layout.randomOutput.representation.encoding.words ≤ 2 * layout.width := by
  have bound := layout.random.output_le
  change layout.random.reply.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤ _ at bound
  change layout.random.reply.representation.encoding.words + (layout.scheme.config.representation.encoding.words +
    layout.scheme.state.representation.encoding.words) ≤ _
  have := layout.config_le; have := layout.core_widths; omega

theorem random_input_fits : layout.randomInput.representation.encoding.words + layout.randomArgs.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := input_widths layout; have := layout.args_le; omega)
theorem hash_input_fits : layout.hashInput.representation.encoding.words + layout.groupArgs.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := input_widths layout; have := layout.args_le; omega)
theorem signing_input_fits : layout.signingInput.representation.encoding.words + layout.groupArgs.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := input_widths layout; have := layout.args_le; omega)

def randomPacket := layout.randomOutput.representation.prod layout.randomArgs.representation
  (layout.fits_of_le (by have := random_output_le layout; have := layout.args_le; omega))
def groupPacket := layout.scalarOutput.representation.prod layout.groupArgs.representation
  (layout.fits_of_le (by have := layout.scalarOutput_le; have := layout.args_le; omega))

def groupInput := layout.hashInput.representation.sum layout.signingInput.representation (width_pos layout.scheme.wordFits)
  (layout.fits_of_le (by have := input_widths layout; have := layout.width_pos; omega))
def input := layout.randomInput.representation.sum (groupInput layout) (width_pos layout.scheme.wordFits)
  (layout.fits_of_le (by
    have := input_widths layout; have := layout.width_pos
    change 1 + max _ (1 + max _ _) ≤ _; omega))
def groupOutput := (groupPacket layout).sum (groupPacket layout) (width_pos layout.scheme.wordFits)
  (layout.fits_of_le (by
    have := layout.scalarOutput_le; have := layout.args_le; have := layout.width_pos
    change 1 + max (_ + _) (_ + _) ≤ _; omega))
def output := (randomPacket layout).sum (groupOutput layout) (width_pos layout.scheme.wordFits)
  (layout.fits_of_le (by
    have := random_output_le layout; have := layout.scalarOutput_le; have := layout.args_le; have := layout.width_pos
    change 1 + max (_ + _) (1 + max (_ + _) (_ + _)) ≤ _; omega))

abbrev Input := layout.randomInput.Value ⊕ (layout.hashInput.Value ⊕ layout.signingInput.Value)
abbrev Output := (layout.randomOutput.Value × layout.randomArgs.Value) ⊕
  ((layout.scalarOutput.Value × layout.groupArgs.Value) ⊕ (layout.scalarOutput.Value × layout.groupArgs.Value))

def randomTag : Realizer .unit (randomPacket layout) (output layout) Sum.inl :=
  inlRealizer .unit (by decide) _ _ layout.scheme.wordFits (output layout).fits
def hashTag : Realizer .unit (groupPacket layout) (output layout) (fun value => .inr (.inl value)) :=
  (inlRealizer .unit (by decide) (groupPacket layout) (groupPacket layout) layout.scheme.wordFits (groupOutput layout).fits).then
    (inrRealizer .unit (by decide) (randomPacket layout) (groupOutput layout) layout.scheme.wordFits (output layout).fits)
def signingTag : Realizer .unit (groupPacket layout) (output layout) (fun value => .inr (.inr value)) :=
  (inrRealizer .unit (by decide) (groupPacket layout) (groupPacket layout) layout.scheme.wordFits (groupOutput layout).fits).then
    (inrRealizer .unit (by decide) (randomPacket layout) (groupOutput layout) layout.scheme.wordFits (output layout).fits)

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler.Dispatch
