import Proofs.Runtime.Caliper.BLSCallerFinishService
import Proofs.Runtime.Caliper.BLSCallerResources

/-! Shared data layouts for an executed BLS caller followed by extraction.
The service is constructed from the extractor's cache/log layout. The terminal
width bound follows from the caller's existing storage bound. -/
namespace Signatures.Runtime.CaliperBackend.BLSCallerExtraction
open Caliper BoundedSource BLSCallerPackets

structure Layouts (w : Nat) (M G F R C A : Type) where
  extraction : TokenEvaluation.Layouts w M G F R
  config : Layout w C
  positive : 0 < extraction.capacity
  serviceFits : 16 * (extraction.rows.accumulation.cache.lookup.width + config.representation.encoding.words +
    extraction.rows.point.representation.encoding.words + 2 * (1 + extraction.capacity *
      (extraction.rows.accumulation.cache.key.representation.encoding.words + extraction.rows.point.representation.encoding.words))) < 2 ^ w
  randomBound : Nat
  randomFits : randomBound + 1 ≤ 2 ^ w
  state : Representation w A
  callerFits : 8 * (1 + state.encoding.words +
    (request (BLSCallerFinish.service extraction config positive serviceFits) randomBound randomFits).encoding.words +
    (reply (BLSCallerFinish.service extraction config positive serviceFits) randomBound randomFits).encoding.words +
    (BLSExtractorFrame.forgery extraction).representation.encoding.words +
    (BLSCallerFinish.service extraction config positive serviceFits).store.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {M G F R C A : Type} (layout : Layouts w M G F R C A)
abbrev service := BLSCallerFinish.service layout.extraction layout.config layout.positive layout.serviceFits
abbrev forgery := BLSExtractorFrame.forgery layout.extraction
abbrev Request := BLSCallerPackets.Request layout.service layout.randomBound
abbrev Reply := BLSCallerPackets.Reply layout.service layout.randomBound
def control : CallerStep.Layouts w A layout.Request layout.Reply layout.forgery.Value layout.service.store.Value :=
  BLSCaller.layout layout.service layout.randomBound layout.randomFits layout.state layout.forgery.representation layout.callerFits
abbrev pending := CallerStep.pending layout.control
abbrev port := UniformQuery.port layout.randomBound layout.service.cache.wordFits layout.randomFits

theorem exitFits : 1 + max layout.forgery.representation.encoding.words layout.pending.encoding.words +
    layout.config.representation.encoding.words + (BLSExtractorFrame.store layout.extraction).representation.encoding.words < 2 ^ w := by
  have fits := (CallerStep.output layout.control).fits
  have sizes := congrArg (fun stored => stored.representation.encoding.words)
    (BLSCallerFinish.service_cacheLogs layout.extraction layout.config layout.positive layout.serviceFits)
  change 1 + max layout.forgery.representation.encoding.words layout.pending.encoding.words +
    (layout.config.representation.encoding.words + layout.service.cacheLogs.representation.encoding.words) < 2 ^ w at fits
  rw [sizes] at fits
  omega

abbrev Packet := (layout.forgery.Value ⊕ (layout.Request × A)) × layout.service.store.Value
def packetView (value : layout.Packet) :=
  BLSCallerFinish.packetView layout.extraction layout.config layout.positive layout.serviceFits value

theorem packet_bytes (value : layout.Packet) :
    (BLSCallerFinish.input layout.extraction layout.config.representation layout.pending layout.exitFits).encoding.encode
        (layout.packetView value) = (CallerStep.output layout.control).encoding.encode value :=
  BLSCallerFinish.packet_bytes layout.extraction layout.config layout.positive layout.serviceFits layout.pending layout.exitFits value

theorem packet_ready {fuel : Nat} {before after : layout.service.store.Value}
    (post : BLSCaller.Postcondition layout.service fuel before after)
    (room : before.val.2.1.length + before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1 ≤
      layout.service.cache.capacityPred + 1) (head : layout.forgery.Value ⊕ (layout.Request × A)) :
    BLSCallerFinish.ready layout.extraction (BLSExtractorFrame.ready layout.extraction) (layout.packetView (head, after)) :=
  BLSCallerFinish.packet_ready layout.extraction layout.config layout.positive layout.serviceFits post room head
end Layouts
end Signatures.Runtime.CaliperBackend.BLSCallerExtraction
