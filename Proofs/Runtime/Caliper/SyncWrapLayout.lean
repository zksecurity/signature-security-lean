import Proofs.Runtime.Caliper.WeightedSharedCaller
import Proofs.Runtime.Caliper.LayoutTools
import Proofs.Runtime.Caliper.ListLayout

/-! Layouts of the known-key wrapper around a weighted caller. The wrapper keeps the known
key `k`, the list of its own hash slots (the attacker's hashes and the hashes it issued before
signing queries, the latter with their correction scalars), and a mode saying where it stands
between two inner steps. Its outer layouts share the inner rows, so requests, replies, hashes
and points have the same representations on both sides; only the capacities, the key and the
caller state change. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull

variable {w : Nat} {K M G F PK A : Type} [Zero F]

/-- Larger transcript capacities for the same rows. -/
structure Capacities (scheme : SharedScheme w K M G F) where
  hashes : Nat
  /-- The hash-coefficient capacity minus one, so the capacity is visibly a successor. -/
  gammaPred : Nat
  goodBounds : ExtractionBounds scheme.rows.good scheme.signs scheme.xi scheme.terms hashes (gammaPred + 1)
  badBounds : ExtractionBounds scheme.rows.bad scheme.signs scheme.xi scheme.terms hashes (gammaPred + 1)
  hashPositive : 0 < hashes
  goodServiceFits : 32 * WeightedCallerFinish.serviceWidth goodBounds.extraction scheme.rows.response.points < 2 ^ w
  badServiceFits : 32 * WeightedCallerFinish.serviceWidth badBounds.extraction scheme.rows.response.config < 2 ^ w

/-- The hash-coefficient capacity. -/
abbrev Capacities.gamma {scheme : SharedScheme w K M G F} (caps : Capacities scheme) : Nat := caps.gammaPred + 1

def enlarge (scheme : SharedScheme w K M G F) (caps : Capacities scheme) : SharedScheme w K M G F where
  rows := scheme.rows
  signs := scheme.signs
  xi := scheme.xi
  terms := scheme.terms
  hashes := caps.hashes
  gamma := caps.gamma
  goodBounds := caps.goodBounds
  badBounds := caps.badBounds
  zeroValid := scheme.zeroValid
  hashPositive := caps.hashPositive
  signPositive := scheme.signPositive
  goodServiceFits := caps.goodServiceFits
  badServiceFits := caps.badServiceFits

/-- The inner caller's layouts, the slot capacity and one storage bound for the wrapper's state. -/
structure Core (w : Nat) (K M G F PK A : Type) [Zero F] where
  inner : SharedLayouts w K M G F PK A
  slotCap : Nat
  /-- Room for the wrapped forgery's representation. -/
  outWords : Nat
  storageFits : 256 * (4 + outWords + inner.good.service.evaluation.coefficient.representation.encoding.words +
    (1 + slotCap * (1 + inner.good.service.evaluation.coefficient.representation.encoding.words)) +
    inner.state.encoding.words + inner.good.service.message.representation.encoding.words +
    inner.good.service.point.representation.encoding.words +
    inner.good.forgery.representation.encoding.words + inner.key.representation.encoding.words +
    (WeightedCallerPackets.request inner.good.service inner.randomBound inner.randomFits).encoding.words +
    (WeightedCallerPackets.reply inner.good.service inner.randomBound inner.randomFits).encoding.words) < 2 ^ w

namespace Core
variable (core : Core w K M G F PK A)

abbrev service := core.inner.good.service
abbrev scalar : Layout w F := core.service.evaluation.coefficient
abbrev message : Layout w M := core.service.message
abbrev point : Layout w G := core.service.point
abbrev keyLayout : Layout w K := core.service.evaluation.cache.key
abbrev forgeryIn := core.inner.good.forgery
include core in
theorem wordFits : 16 < 2 ^ w := core.service.evaluation.cache.wordFits
abbrev requestRep := WeightedCallerPackets.request core.service core.inner.randomBound core.inner.randomFits
abbrev replyRep := WeightedCallerPackets.reply core.service core.inner.randomBound core.inner.randomFits
def width : Nat := 4 + core.outWords + core.scalar.representation.encoding.words +
  (1 + core.slotCap * (1 + core.scalar.representation.encoding.words)) +
  core.inner.state.encoding.words + core.message.representation.encoding.words +
  core.point.representation.encoding.words + core.forgeryIn.representation.encoding.words +
  core.inner.key.representation.encoding.words + core.requestRep.encoding.words + core.replyRep.encoding.words
theorem fits {n : Nat} (bound : n ≤ 256 * core.width) : n < 2 ^ w := bound.trans_lt core.storageFits

/-! Carriers with their certificates: the wrapper's own values are layout values. -/
abbrev scalarAll : Layout w core.scalar.Value := Layout.all core.scalar.representation
abbrev messageAll : Layout w core.message.Value := Layout.all core.message.representation
abbrev pointAll : Layout w core.point.Value := Layout.all core.point.representation
abbrev keyAll : Layout w core.keyLayout.Value := Layout.all core.keyLayout.representation
abbrev forgeryAll : Layout w core.forgeryIn.Value := Layout.all core.forgeryIn.representation
abbrev stateAll : Layout w A := Layout.all core.inner.state
theorem scalarAll_words : core.scalarAll.representation.encoding.words = core.scalar.representation.encoding.words := rfl
theorem messageAll_words : core.messageAll.representation.encoding.words = core.message.representation.encoding.words := rfl
theorem pointAll_words : core.pointAll.representation.encoding.words = core.point.representation.encoding.words := rfl
theorem forgeryAll_words : core.forgeryAll.representation.encoding.words = core.forgeryIn.representation.encoding.words := rfl
theorem stateAll_words : core.stateAll.representation.encoding.words = core.inner.state.encoding.words := rfl

/-- A hash slot: the attacker's own hash, or a hash issued before signing with its correction. -/
abbrev slotEntry : Layout w (Unit ⊕ F) :=
  (DataImplementation.unitLayout w).sum core.scalar (width_pos core.wordFits)
    (core.fits (by change 1 + max 0 _ ≤ _; rw [Nat.zero_max]; unfold width; omega))
theorem slotEntry_words : core.slotEntry.representation.encoding.words = 1 + core.scalar.representation.encoding.words := by
  change 1 + max 0 _ = _; rw [Nat.zero_max]
abbrev slots : Layout w (List (Unit ⊕ F)) :=
  core.slotEntry.boundedList core.slotCap (core.fits (by unfold width; nlinarith))
    (by rw [slotEntry_words]; exact core.fits (by unfold width; omega))
theorem slots_words : core.slots.representation.encoding.words = 1 + core.slotCap * (1 + core.scalar.representation.encoding.words) := by
  change 1 + core.slotCap * core.slotEntry.representation.encoding.words = _
  rw [slotEntry_words]
/-- The known key beside the slots. -/
abbrev keyed : Layout w (core.scalar.Value × List (Unit ⊕ F)) :=
  core.scalarAll.prod core.slots (by rw [slots_words, scalarAll_words]; exact core.fits (by unfold width; omega))
theorem keyed_words : core.keyed.representation.encoding.words =
    core.scalar.representation.encoding.words + (1 + core.slotCap * (1 + core.scalar.representation.encoding.words)) := by
  change core.scalarAll.representation.encoding.words + core.slots.representation.encoding.words = _
  rw [slots_words]; rfl
/-- The inner caller asked to sign and waits for the period's hash. -/
abbrev preSign : Layout w (core.message.Value × A) := core.messageAll.prod core.stateAll (core.fits (by
  have := core.stateAll_words; have := core.messageAll_words; unfold width; omega))
/-- The hash arrived; the signing query is pending. -/
abbrev afterHash : Layout w ((core.message.Value × core.point.Value) × A) :=
  (core.messageAll.prod core.pointAll (core.fits (by have := core.messageAll_words; have := core.pointAll_words; unfold width; omega))).prod
    core.stateAll (core.fits (by
      have := core.stateAll_words; have := core.messageAll_words; have := core.pointAll_words
      change (_ + _) + _ ≤ _; unfold width; omega))
abbrev tail₂ : Layout w (((core.message.Value × core.point.Value) × A) ⊕ core.forgeryIn.Value) :=
  core.afterHash.sum core.forgeryAll (width_pos core.wordFits) (core.fits (by
    have := core.stateAll_words; have := core.messageAll_words; have := core.pointAll_words; have := core.forgeryAll_words
    change 1 + max ((_ + _) + _) _ ≤ _; unfold width; omega))
abbrev tail₁ : Layout w ((core.message.Value × A) ⊕ (((core.message.Value × core.point.Value) × A) ⊕ core.forgeryIn.Value)) :=
  core.preSign.sum core.tail₂ (width_pos core.wordFits) (core.fits (by
    have := core.stateAll_words; have := core.messageAll_words; have := core.pointAll_words; have := core.forgeryAll_words
    change 1 + max (_ + _) (1 + max ((_ + _) + _) _) ≤ _; unfold width; omega))
/-- Where the wrapper stands: forwarding (inner state), before a signing hash, before the
signing query, or before the final hash. -/
abbrev mode : Layout w (A ⊕ ((core.message.Value × A) ⊕ (((core.message.Value × core.point.Value) × A) ⊕ core.forgeryIn.Value))) :=
  core.stateAll.sum core.tail₁ (width_pos core.wordFits) (core.fits (by
    have := core.stateAll_words; have := core.messageAll_words; have := core.pointAll_words; have := core.forgeryAll_words
    change 1 + max _ (1 + max (_ + _) (1 + max ((_ + _) + _) _)) ≤ _; unfold width; omega))
theorem mode_words : core.mode.representation.encoding.words ≤ 3 + core.width := by
  have := core.stateAll_words; have := core.messageAll_words; have := core.pointAll_words; have := core.forgeryAll_words
  change 1 + max _ (1 + max (_ + _) (1 + max ((_ + _) + _) _)) ≤ _; unfold width; omega
/-- The wrapper's caller state. -/
abbrev wrapper : Layout w ((core.scalar.Value × List (Unit ⊕ F)) ×
    (A ⊕ ((core.message.Value × A) ⊕ (((core.message.Value × core.point.Value) × A) ⊕ core.forgeryIn.Value)))) :=
  core.keyed.prod core.mode (by
    have := core.mode_words
    have := core.keyed_words
    exact core.fits (by unfold width at *; omega))
theorem wrapper_words : core.wrapper.representation.encoding.words ≤ 4 + 2 * core.width := by
  have := core.mode_words
  have := core.keyed_words
  change core.keyed.representation.encoding.words + core.mode.representation.encoding.words ≤ _
  unfold width at *
  omega
/-- The wrapper's key: the inner public key and the known exponent. -/
abbrev key : Layout w (PK × F) := core.inner.key.prod core.scalar (by
  have := core.inner.samplingFits
  have := core.wordFits
  show core.inner.key.representation.encoding.words + core.inner.scheme.rows.accumulation.cache.value.representation.encoding.words < 2 ^ w
  omega)
end Core

/-- The wrapper's layouts: outer capacities and the storage bounds of the outer shared layouts. -/
structure Wrapper (core : Core w K M G F PK A) where
  caps : Capacities core.inner.scheme
  goodCallerFits : 8 * (1 + core.wrapper.representation.encoding.words +
    (WeightedCallerPackets.request (enlarge core.inner.scheme caps).goodService core.inner.randomBound core.inner.randomFits).encoding.words +
    (WeightedCallerPackets.reply (enlarge core.inner.scheme caps).goodService core.inner.randomBound core.inner.randomFits).encoding.words +
    caps.goodBounds.extraction.forgery.representation.encoding.words +
    (enlarge core.inner.scheme caps).goodService.store.representation.encoding.words) < 2 ^ w
  badCallerFits : 8 * (1 + core.wrapper.representation.encoding.words +
    (WeightedCallerPackets.request (enlarge core.inner.scheme caps).badService core.inner.randomBound core.inner.randomFits).encoding.words +
    (WeightedCallerPackets.reply (enlarge core.inner.scheme caps).badService core.inner.randomBound core.inner.randomFits).encoding.words +
    caps.badBounds.extraction.forgery.representation.encoding.words +
    (enlarge core.inner.scheme caps).badService.store.representation.encoding.words) < 2 ^ w
  goodSetupFits : 16 * ((enlarge core.inner.scheme caps).goodService.store.representation.encoding.words +
    core.inner.scheme.rows.response.points.representation.encoding.words + 2 * core.key.representation.encoding.words) < 2 ^ w
  badSetupFits : 16 * ((enlarge core.inner.scheme caps).badService.store.representation.encoding.words +
    core.inner.scheme.rows.response.config.representation.encoding.words + 2 * core.key.representation.encoding.words) < 2 ^ w
  samplingFits : 16 * (core.inner.scheme.rows.accumulation.cache.value.representation.encoding.words +
    core.inner.scheme.rows.response.points.representation.encoding.words + 2 * core.key.representation.encoding.words) < 2 ^ w
  /-- The outer forgery's hash coefficients hold every slot and the final hash. -/
  gammaRoom : core.slotCap ≤ caps.gammaPred

namespace Wrapper
variable {core : Core w K M G F PK A} (wrapper : Wrapper core)

/-- The outer shared layouts: the inner rows, the enlarged capacities, the wrapped key and state. -/
def outer : SharedLayouts w K M G F (PK × F) core.wrapper.Value where
  scheme := enlarge core.inner.scheme wrapper.caps
  key := core.key
  state := core.wrapper.representation
  randomBound := core.inner.randomBound
  randomFits := core.inner.randomFits
  goodCallerFits := wrapper.goodCallerFits
  badCallerFits := wrapper.badCallerFits
  goodSetupFits := wrapper.goodSetupFits
  badSetupFits := wrapper.badSetupFits
  samplingFits := wrapper.samplingFits

/-- Requests and replies are shared between the inner and outer layouts. -/
theorem request_eq : wrapper.outer.good.Request = core.inner.good.Request := rfl
theorem reply_eq : wrapper.outer.good.Reply = core.inner.good.Reply := rfl
theorem request_representation :
    WeightedCallerPackets.request wrapper.outer.good.service wrapper.outer.randomBound wrapper.outer.randomFits =
      WeightedCallerPackets.request core.inner.good.service core.inner.randomBound core.inner.randomFits := rfl
theorem reply_representation :
    WeightedCallerPackets.reply wrapper.outer.good.service wrapper.outer.randomBound wrapper.outer.randomFits =
      WeightedCallerPackets.reply core.inner.good.service core.inner.randomBound core.inner.randomFits := rfl
end Wrapper

end Signatures.Runtime.CaliperBackend.SyncWrap
