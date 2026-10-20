import Signatures.Runtime.Caliper.WeightedCallerFinishService
import Signatures.Runtime.Caliper.WeightedCallerResources

/-! Shared data layouts for an executed weighted caller followed by extraction.
The service is constructed from the extractor's independent cache/log layouts. The terminal
width bound follows from the caller's existing storage bound. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerExtraction
open Caliper BoundedSource WeightedCallerPackets

structure Layouts (w : Nat) (K M G F R C A : Type) where
  extraction : WeightedExtractor.Layouts w K M G F R
  config : Layout w C
  zero : extraction.signing.rows.accumulation.cache.value.Value
  default : extraction.signing.rows.accumulation.cache.value.Value
  hashPositive : 0 < extraction.hashCapacity
  signPositive : 0 < extraction.signing.capacity
  serviceFits : 32 * WeightedCallerFinish.serviceWidth extraction config < 2 ^ w
  randomBound : Nat
  randomFits : randomBound + 1 ≤ 2 ^ w
  state : Representation w A
  callerFits : 8 * (1 + state.encoding.words +
    (request (WeightedCallerFinish.service extraction config zero default hashPositive signPositive serviceFits) randomBound randomFits).encoding.words +
    (reply (WeightedCallerFinish.service extraction config zero default hashPositive signPositive serviceFits) randomBound randomFits).encoding.words +
    extraction.forgery.representation.encoding.words +
    (WeightedCallerFinish.service extraction config zero default hashPositive signPositive serviceFits).store.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {K M G F R C A : Type} (layout : Layouts w K M G F R C A)
abbrev service := WeightedCallerFinish.service layout.extraction layout.config layout.zero layout.default layout.hashPositive layout.signPositive layout.serviceFits
abbrev terms := layout.extraction.signing.terms
abbrev termCountFits := layout.extraction.signing.termCountFits
abbrev termStorageFits := layout.extraction.signing.termStorageFits
abbrev forgery := layout.extraction.forgery
abbrev Request := WeightedCallerPackets.Request layout.service layout.randomBound
abbrev Reply := WeightedCallerPackets.Reply layout.service layout.randomBound
def control : CallerStep.Layouts w A layout.Request layout.Reply layout.forgery.Value layout.service.store.Value :=
  WeightedCaller.layout layout.service layout.randomBound layout.randomFits layout.state layout.forgery.representation layout.callerFits
abbrev pending := CallerStep.pending layout.control
abbrev port := UniformQuery.port layout.randomBound layout.service.evaluation.cache.wordFits layout.randomFits

theorem exitFits : 1 + max layout.forgery.representation.encoding.words layout.pending.encoding.words +
    layout.config.representation.encoding.words + (layout.extraction.store).representation.encoding.words < 2 ^ w := by
  have fits := (CallerStep.output layout.control).fits
  have sizes := congrArg (fun stored => stored.representation.encoding.words)
    (WeightedCallerFinish.service_cacheLogs layout.extraction layout.config layout.zero layout.default layout.hashPositive layout.signPositive layout.serviceFits)
  change 1 + max layout.forgery.representation.encoding.words layout.pending.encoding.words +
    (layout.config.representation.encoding.words + layout.service.signing.cacheLogs.representation.encoding.words) < 2 ^ w at fits
  rw [sizes] at fits
  omega

abbrev Packet := (layout.forgery.Value ⊕ (layout.Request × A)) × layout.service.store.Value
def packetView (value : layout.Packet) :=
  WeightedCallerFinish.packetView layout.extraction layout.config layout.zero layout.default layout.hashPositive layout.signPositive layout.serviceFits value

theorem packet_bytes (value : layout.Packet) :
    (WeightedCallerFinish.input layout.extraction layout.config.representation layout.pending layout.exitFits).encoding.encode
        (layout.packetView value) = (CallerStep.output layout.control).encoding.encode value :=
  WeightedCallerFinish.packet_bytes layout.extraction layout.config layout.zero layout.default layout.hashPositive layout.signPositive layout.serviceFits layout.pending layout.exitFits value

theorem packet_ready {fuel : Nat} {before after : layout.service.store.Value}
    (post : WeightedCaller.Postcondition layout.service layout.extraction.signing.terms fuel before after)
    (room : before.val.2.1.length + max 1 layout.extraction.signing.terms *
      (before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1) ≤
      layout.service.evaluation.cache.capacityPred + 1) (head : layout.forgery.Value ⊕ (layout.Request × A)) :
    WeightedCallerFinish.ready layout.extraction layout.extraction.ready (layout.packetView (head, after)) :=
  WeightedCallerFinish.packet_ready layout.extraction layout.config layout.zero layout.default layout.hashPositive layout.signPositive layout.serviceFits post room head
end Layouts
end Signatures.Runtime.CaliperBackend.WeightedCallerExtraction
