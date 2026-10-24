import Proofs.Runtime.Caliper.BLSCallerExtractionResources
import Proofs.Runtime.Caliper.BLSSetupResources

/-! Shared layouts for complete BLS AGM programs. Setup, query service and
extraction are built from one scalar cache and transcript capacity. Their store
representations agree definitionally; no caller/setup compatibility premise is
needed. All combined address-width bounds remain explicit. -/
namespace Signatures.Runtime.CaliperBackend.BLSFull
open Caliper BoundedSource

structure Scheme (w : Nat) (M F G : Type) where
  tokens : BLSTokens.Layouts w M G F
  positive : 0 < tokens.capacity
  responseFits : 16 * (tokens.rows.accumulation.cache.value.representation.encoding.words +
    tokens.rows.point.representation.encoding.words) < 2 ^ w
  goodFits : 16 * (tokens.rows.accumulation.cache.lookup.width + 3 * tokens.rows.point.representation.encoding.words +
    2 * (1 + tokens.capacity * (tokens.rows.accumulation.cache.key.representation.encoding.words +
      tokens.rows.point.representation.encoding.words))) < 2 ^ w
  badFits : 16 * ((tokens.rows.accumulation.cache.pairValues tokens.rows.accumulation.pairStorageFits).lookup.width +
    tokens.rows.accumulation.cache.value.representation.encoding.words + 3 * tokens.rows.point.representation.encoding.words +
    2 * (1 + tokens.capacity * (tokens.rows.accumulation.cache.key.representation.encoding.words +
      tokens.rows.point.representation.encoding.words))) < 2 ^ w

namespace Scheme
variable {w : Nat} {M F G : Type} (layout : Scheme w M F G)
def service : BLSReply.SchemeLayouts w M F G where
  cache := layout.tokens.rows.accumulation.cache
  point := layout.tokens.rows.point
  responseFits := layout.responseFits
  capacityPred := layout.tokens.capacity - 1
  countFits := by have := layout.tokens.counterFits; have := layout.positive; omega
  goodFits := by simpa only [Nat.sub_add_cancel layout.positive] using layout.goodFits
  pairFits := layout.tokens.rows.accumulation.pairStorageFits
  badFits := by simpa only [Nat.sub_add_cancel layout.positive] using layout.badFits

theorem good_service_fits : 16 * (layout.tokens.good.rows.accumulation.cache.lookup.width +
    layout.service.good.config.representation.encoding.words + layout.tokens.good.rows.point.representation.encoding.words +
    2 * (1 + layout.tokens.good.capacity * (layout.tokens.good.rows.accumulation.cache.key.representation.encoding.words +
      layout.tokens.good.rows.point.representation.encoding.words))) < 2 ^ w := by
  have fit := layout.goodFits
  change 16 * (layout.tokens.rows.accumulation.cache.lookup.width +
    (layout.tokens.rows.point.representation.encoding.words + layout.tokens.rows.point.representation.encoding.words) +
    layout.tokens.rows.point.representation.encoding.words +
    2 * (1 + layout.tokens.capacity * (layout.tokens.rows.accumulation.cache.key.representation.encoding.words +
      layout.tokens.rows.point.representation.encoding.words))) < 2 ^ w
  omega

theorem bad_service_fits : 16 * (layout.tokens.bad.rows.accumulation.cache.lookup.width +
    layout.service.bad.config.representation.encoding.words + layout.tokens.bad.rows.point.representation.encoding.words +
    2 * (1 + layout.tokens.bad.capacity * (layout.tokens.bad.rows.accumulation.cache.key.representation.encoding.words +
      layout.tokens.bad.rows.point.representation.encoding.words))) < 2 ^ w := by
  have fit := layout.badFits
  change 16 * ((layout.tokens.rows.accumulation.cache.pairValues layout.tokens.rows.accumulation.pairStorageFits).lookup.width +
    (layout.tokens.rows.accumulation.cache.value.representation.encoding.words +
      (layout.tokens.rows.point.representation.encoding.words + layout.tokens.rows.point.representation.encoding.words)) +
    layout.tokens.rows.point.representation.encoding.words +
    2 * (1 + layout.tokens.capacity * (layout.tokens.rows.accumulation.cache.key.representation.encoding.words +
      layout.tokens.rows.point.representation.encoding.words))) < 2 ^ w
  omega
end Scheme

structure Layouts (w : Nat) (M F G K A : Type) where
  shared : Scheme w M F G
  key : Layout w K
  setupFits : 16 * (shared.service.good.store.representation.encoding.words + shared.service.bad.store.representation.encoding.words +
    2 * key.representation.encoding.words + 2 * shared.service.cache.value.representation.encoding.words +
    4 * shared.service.point.representation.encoding.words) < 2 ^ w
  randomBound : Nat
  randomFits : randomBound + 1 ≤ 2 ^ w
  state : Representation w A
  goodCallerFits : 8 * (1 + state.encoding.words +
    (BLSCallerPackets.request shared.service.good randomBound randomFits).encoding.words +
    (BLSCallerPackets.reply shared.service.good randomBound randomFits).encoding.words +
    (BLSExtractorFrame.forgery shared.tokens.good).representation.encoding.words +
    shared.service.good.store.representation.encoding.words) < 2 ^ w
  badCallerFits : 8 * (1 + state.encoding.words +
    (BLSCallerPackets.request shared.service.bad randomBound randomFits).encoding.words +
    (BLSCallerPackets.reply shared.service.bad randomBound randomFits).encoding.words +
    (BLSExtractorFrame.forgery shared.tokens.bad).representation.encoding.words +
    shared.service.bad.store.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {M F G K A : Type} (layout : Layouts w M F G K A)
abbrev tokens := layout.shared.tokens
abbrev scheme := layout.shared.service
def setup : BLSSetup.Layouts w M F G K := ⟨layout.scheme, layout.key, layout.setupFits⟩
def good : BLSCallerExtraction.Layouts w M G F F (G × G) A where
  extraction := layout.tokens.good
  config := layout.scheme.good.config
  positive := layout.shared.positive
  serviceFits := layout.shared.good_service_fits
  randomBound := layout.randomBound
  randomFits := layout.randomFits
  state := layout.state
  callerFits := layout.goodCallerFits
def bad : BLSCallerExtraction.Layouts w M G F (F × F) (F × (G × G)) A where
  extraction := layout.tokens.bad
  config := layout.scheme.bad.config
  positive := layout.shared.positive
  serviceFits := layout.shared.bad_service_fits
  randomBound := layout.randomBound
  randomFits := layout.randomFits
  state := layout.state
  callerFits := layout.badCallerFits

theorem good_service : layout.good.service = layout.scheme.good := rfl
theorem bad_service : layout.bad.service = layout.scheme.bad := rfl
abbrev port := layout.good.port
abbrev Forgery := layout.good.forgery.Value
abbrev Request := layout.good.Request
abbrev Reply := layout.good.Reply
abbrev Next := Forgery layout ⊕ (Request layout × A)
def goodInput := layout.key.representation.prod layout.good.service.store.representation layout.setup.goodFits
def badInput := layout.key.representation.prod layout.bad.service.store.representation layout.setup.badFits

def goodSetupView (value : layout.setup.goodOutput.Value) : layout.key.Value × layout.good.service.store.Value :=
  productView layout.key layout.scheme.good.store value
def badSetupView (value : layout.setup.badOutput.Value) : layout.key.Value × layout.bad.service.store.Value :=
  productView layout.key layout.scheme.bad.store value
theorem good_setup_bytes (value : layout.setup.goodOutput.Value) :
    layout.goodInput.encoding.encode (layout.goodSetupView value) = layout.setup.goodOutput.representation.encoding.encode value := rfl
theorem bad_setup_bytes (value : layout.setup.badOutput.Value) :
    layout.badInput.encoding.encode (layout.badSetupView value) = layout.setup.badOutput.representation.encoding.encode value := rfl
end Layouts
end Signatures.Runtime.CaliperBackend.BLSFull
