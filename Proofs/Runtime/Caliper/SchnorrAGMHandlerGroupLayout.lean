import Proofs.Runtime.Caliper.SchnorrAGMHandlerLayout

/-! Common-store hash/signing inputs keep each core's conditional admission
predicate. Rejected requests do not acquire an unnecessary free-slot guard. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler
open Caliper BoundedSource
abbrev GroupRequest (M F G : Type) := (M × List G × List (List F)) ×
  (G × G) × Signatures.Runtime.SchnorrAGM.Native.EncodedState F G M
def hashArgument {M F G : Type} (args : GroupRequest M F G) : HashDispatch.Input M F G :=
  (args.1.1, args.1.2.1, args.1.2.2, args.2.2)
def signingArgument {M F G : Type} (args : GroupRequest M F G) : SigningDispatch.Input M F G :=
  (args.1.2.1, args.1.2.2, args.2.1.1, args.2.1.2, args.1.1, args.2.2)

namespace Layouts
variable {w qH qS randomBound : Nat} {M F G : Type} (layout : Layouts w M F G qH qS randomBound)

def signingInput := layout.groupInput.restrict (fun args => layout.signing.admissible (signingArgument args))
def signingValue (args : layout.signingInput.Value) : layout.signing.input.Value :=
  ⟨signingArgument args.val, ⟨args.property.1.1.2.1, args.property.1.1.2.2,
    args.property.1.2.1.1, args.property.1.2.1.2, args.property.1.1.1, args.property.1.2.2⟩, args.property.2⟩
theorem signing_input_words : layout.signing.input.representation.encoding.words =
    ((layout.lists.representation.encoding.words + layout.scheme.config.representation.encoding.words) +
      layout.scheme.message.representation.encoding.words) + layout.scheme.state.representation.encoding.words := by
  change layout.points.representation.encoding.words + (layout.coefficientRows.representation.encoding.words +
    (layout.scheme.point.representation.encoding.words + (layout.scheme.point.representation.encoding.words +
      (layout.scheme.message.representation.encoding.words + layout.scheme.state.representation.encoding.words)))) =
      (((layout.points.representation.encoding.words + layout.coefficientRows.representation.encoding.words) +
        (layout.scheme.point.representation.encoding.words + layout.scheme.point.representation.encoding.words)) +
          layout.scheme.message.representation.encoding.words) + layout.scheme.state.representation.encoding.words
  omega
theorem scalarOutput_le : layout.scalarOutput.representation.encoding.words ≤ 2 * layout.width := by
  have bound := layout.signing.output_le
  change layout.signing.reply.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤ _ at bound
  change layout.signing.reply.representation.encoding.words +
    (layout.scheme.config.representation.encoding.words + layout.scheme.state.representation.encoding.words) ≤ _
  have := layout.config_le; have := layout.core_widths; omega
theorem readOutput_le : (Read.output layout.scheme).representation.encoding.words ≤ layout.width := by
  have bound := layout.signing.output_le
  change (layout.scheme.scalar.representation.encoding.words + layout.signing.replyPoints.representation.encoding.words) +
    layout.scheme.state.representation.encoding.words ≤ _ at bound
  change layout.scheme.scalar.representation.encoding.words + layout.scheme.state.representation.encoding.words ≤ _
  have := layout.core_widths; omega

theorem signingInputFits : layout.signing.input.representation.encoding.words +
    layout.scheme.config.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.signing.input_le; have := layout.core_widths; have := layout.config_le; omega)
theorem signingOutputFits : layout.signing.output.representation.encoding.words +
    layout.scheme.config.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.signing.output_le; have := layout.core_widths; have := layout.config_le; omega)
def signingPrepared := layout.signing.input.representation.prod layout.scheme.config.representation layout.signingInputFits
def signingFinished := layout.signing.output.representation.prod layout.scheme.config.representation layout.signingOutputFits

variable [DecidableEq M] [DecidableEq G]
def hashInput := layout.groupInput.restrict (fun args => layout.hash.admissible (hashArgument args))
def hashValue (args : layout.hashInput.Value) : layout.hash.input.Value :=
  ⟨hashArgument args.val, ⟨args.property.1.1.1, args.property.1.1.2.1,
    args.property.1.1.2.2, args.property.1.2.2⟩, args.property.2⟩
theorem hash_input_words : layout.hash.input.representation.encoding.words =
    layout.groupArgs.representation.encoding.words + layout.scheme.state.representation.encoding.words := by
  change layout.scheme.message.representation.encoding.words + (layout.points.representation.encoding.words +
    (layout.coefficientRows.representation.encoding.words + layout.scheme.state.representation.encoding.words)) =
      (layout.scheme.message.representation.encoding.words + (layout.points.representation.encoding.words +
        layout.coefficientRows.representation.encoding.words)) + layout.scheme.state.representation.encoding.words
  omega
theorem hashInputFits : layout.hash.input.representation.encoding.words +
    layout.scheme.config.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.hash.input_le; have := layout.core_widths; have := layout.config_le; omega)
def hashPrepared := layout.hash.input.representation.prod layout.scheme.config.representation layout.hashInputFits

omit [DecidableEq M] [DecidableEq G] in
theorem hashOutputFits : (Read.output layout.scheme).representation.encoding.words +
    layout.scheme.config.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.readOutput_le; have := layout.config_le; omega)
def hashFinished := (Read.output layout.scheme).representation.prod layout.scheme.config.representation layout.hashOutputFits

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.Handler
