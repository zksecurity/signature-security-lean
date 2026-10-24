import Proofs.Runtime.Caliper.CoronCallerFinishBounds
import Proofs.Runtime.Caliper.BLSCallerResources

/-! Shared caller/service layouts for co-CDH. The caller returns an ordinary
message/signature pair; its output is exactly the terminal handler's input.
Cache and log reservations are numerical bounds on represented stored data. -/
namespace Signatures.Runtime.CaliperBackend.CoronCaller
open Caliper BoundedSource
variable {w randomBound : Nat} {qS : Fin (randomBound + 1)} {M F G A U : Type}

structure Layouts (service : CoronService.Layouts w M F G randomBound qS) (A U : Type) where
  state : Representation w A
  input : Representation w U
  callerFits : 8 * (1 + state.encoding.words +
    (BLSCallerPackets.request service.service randomBound service.randomFits).encoding.words +
    (BLSCallerPackets.reply service.service randomBound service.randomFits).encoding.words +
    (CoronTerminalFrame.forgery service).representation.encoding.words + service.service.store.representation.encoding.words) < 2 ^ w
  inputFits : input.encoding.words + service.service.store.representation.encoding.words < 2 ^ w

namespace Layouts
variable {service : CoronService.Layouts w M F G randomBound qS} (layout : Layouts service A U)
abbrev Request (_layout : Layouts service A U) := BLSCallerPackets.Request service.service randomBound
abbrev Reply (_layout : Layouts service A U) := BLSCallerPackets.Reply service.service randomBound
abbrev Forgery (_layout : Layouts service A U) := (CoronTerminalFrame.forgery service).Value
abbrev Next := layout.Forgery ⊕ (layout.Request × A)
abbrev Packet := layout.Next × service.service.store.Value
def control := BLSCaller.layout service.service randomBound service.randomFits layout.state
  (CoronTerminalFrame.forgery service).representation layout.callerFits
abbrev pending := CallerStep.pending layout.control
def incoming : Representation w (U × service.service.store.Value) :=
  layout.input.prod service.service.store.representation layout.inputFits
theorem exitFits : 1 + max (CoronTerminalFrame.forgery service).representation.encoding.words layout.pending.encoding.words +
    service.service.store.representation.encoding.words < 2 ^ w := (CallerStep.output layout.control).fits
theorem finish_input : CoronCallerFinish.input service layout.pending layout.exitFits = CallerStep.output layout.control := rfl

def ready (_layout : Layouts service A U) (fuel : Nat) (value : U × service.service.store.Value) : Prop :=
  value.2.val.2.1.length + fuel + 1 ≤ service.service.cache.capacityPred + 1 ∧
    value.2.val.2.2.1.length + value.2.val.2.2.2.length + fuel ≤ service.service.capacityPred + 1
instance (fuel : Nat) : DecidablePred (layout.ready fuel) := fun _ => inferInstanceAs (Decidable (_ ∧ _))
def admitted (fuel : Nat) : Layout w (U × service.service.store.Value) where
  valid := layout.ready fuel
  representation := layout.incoming.restrict (layout.ready fuel)
theorem reserved {fuel : Nat} {value : U × service.service.store.Value} (valid : layout.ready fuel value) :
    BLSReply.Reserved service.service fuel value.2.val :=
  ⟨value.2.property.1, value.2.property.2.1.2,
    ⟨value.2.property.2.2.1.2, value.2.property.2.2.2.2⟩, by have := valid.1; omega, valid.2⟩
end Layouts

variable {service : CoronService.Layouts w M F G randomBound qS} (layout : Layouts service A U)
/-- Only local attacker steps are supplied. Oracle handling and the controller
that retains private state are generated from these steps. -/
structure Caller where
  advance : A × layout.Reply → layout.Next
  continuation : Realizer .unit (CallerStep.resume layout.control) (CallerStep.next layout.control) advance
  localNameFits : continuation.savedBuffer < 2 ^ w
  initial : U → layout.Next
  initialCode : Realizer .unit layout.input (CallerStep.next layout.control) initial
  initialNameFits : initialCode.savedBuffer < 2 ^ w

structure Caller.Invariant (caller : Caller layout) (fuel : Nat) where
  domain : Nat → layout.Request × A → Prop
  advance : ∀ remaining q c, domain (remaining + 1) (q, c) →
    ∀ represented original, BLSCallerHandler.replyMatches service.service randomBound q represented original →
      BLSCaller.HeadValid service.service randomBound domain remaining (caller.advance (c, represented))
  initial : ∀ value, BLSCaller.HeadValid service.service randomBound domain fuel (caller.initial value)

structure Caller.Bounds (caller : Caller layout) where
  stepTime : Nat
  stepWords : Nat
  initialTime : Nat
  initialWords : Nat
  step_time : ∀ value, caller.continuation.time value ≤ stepTime
  step_words : descriptionWords caller.continuation.code ≤ stepWords
  initial_time : ∀ value, caller.initialCode.time value ≤ initialTime
  initial_words : descriptionWords caller.initialCode.code ≤ initialWords
  slots : Nat
  step_names : NamesAccounted caller.continuation.code slots
  initial_names : NamesAccounted caller.initialCode.code slots

end Signatures.Runtime.CaliperBackend.CoronCaller
