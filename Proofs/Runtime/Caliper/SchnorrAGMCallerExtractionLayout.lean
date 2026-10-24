import Proofs.Runtime.Caliper.SchnorrAGMCallerFinishBounds
import Proofs.Runtime.Caliper.SchnorrAGMCallerResources

/-! The generated caller and terminal use the same finite store and represented
forgery. The caller's existing storage bound admits the terminal frame, and its
proved postcondition supplies cache room without an additional exit contract. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerExtraction
open Caliper BoundedSource CallerPackets

structure Layouts (w : Nat) (M F G : Type) (qH qS randomBound : Nat) (A : Type) where
  service : Handler.Layouts w M F G qH qS randomBound
  state : Representation w A
  callerFits : 8 * (1 + state.encoding.words + (request service).encoding.words + (reply service).encoding.words +
    (CallerFinish.forgery service.hash).representation.encoding.words + service.scheme.store.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w qH qS randomBound : Nat} {M F G A : Type} (layout : Layouts w M F G qH qS randomBound A)
abbrev forgery := CallerFinish.forgery layout.service.hash
abbrev Request := CallerPackets.Request layout.service
abbrev Reply := CallerPackets.Reply layout.service
def control : CallerStep.Layouts w A layout.Request layout.Reply layout.forgery.Value layout.service.scheme.store.Value :=
  Caller.layout layout.service layout.state layout.forgery.representation layout.callerFits
abbrev pending := CallerStep.pending layout.control
abbrev Packet := (layout.forgery.Value ⊕ (layout.Request × A)) × layout.service.scheme.store.Value
theorem exitFits : 1 + max layout.forgery.representation.encoding.words layout.pending.encoding.words +
    layout.service.scheme.store.representation.encoding.words < 2 ^ w :=
  (CallerStep.output layout.control).fits
theorem packet_bytes (value : layout.Packet) :
    (CallerFinish.input layout.service.hash layout.pending layout.exitFits).encoding.encode value =
      (CallerStep.output layout.control).encoding.encode value := rfl

variable [Field F] [DecidableEq M] [DecidableEq G]
theorem packet_ready {before after : layout.service.scheme.store.Value}
    (post : Caller.Postcondition layout.service before after)
    (head : layout.forgery.Value ⊕ (layout.Request × A)) :
    CallerFinish.ready layout.service.hash (head, after) := by
  cases head with
  | inl forgery =>
    exact CallerFinish.admitted_of_room layout.service.hash (forgery, after)
      (by change after.val.2.1.length ≤ qH + qS; have := post.extraction_room; omega)
  | inr pending => trivial

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrAGM.CallerExtraction
