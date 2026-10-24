import Proofs.Runtime.Caliper.BLSCallerFinish
import Proofs.Runtime.Caliper.BLSCallerPostcondition

/-! A caller service and extractor share their cache, token encodings and log
capacity. Configuration is an additional bounded stored value. The bridge to
the terminal frame changes only equal-byte mathematical product views; the
actual removal of configuration and union padding remains executed routing. -/
namespace Signatures.Runtime.CaliperBackend.BLSCallerFinish
open Caliper BoundedSource
variable {w : Nat} {M G F R C : Type} (layout : TokenEvaluation.Layouts w M G F R)
    (configuration : Layout w C) (positive : 0 < layout.capacity)
    (serviceFits : 16 * (layout.rows.accumulation.cache.lookup.width + configuration.representation.encoding.words +
      layout.rows.point.representation.encoding.words + 2 * (1 + layout.capacity *
        (layout.rows.accumulation.cache.key.representation.encoding.words + layout.rows.point.representation.encoding.words))) < 2 ^ w)

def service : BLSReply.Layouts w M R C G where
  cache := layout.rows.accumulation.cache
  point := layout.rows.point
  config := configuration
  capacityPred := layout.capacity - 1
  countFits := by have := layout.countFits; omega
  storageFits := by simpa only [Nat.sub_add_cancel positive] using serviceFits

theorem service_log : (service layout configuration positive serviceFits).records.log = BLSExtractorFrame.tokens layout := by
  unfold BLSReply.Layouts.records BLSRecord.Layouts.log
  dsimp only [service]
  simp only [Nat.sub_add_cancel positive]
  rfl
theorem service_cacheLogs : (service layout configuration positive serviceFits).cacheLogs = BLSExtractorFrame.store layout := by
  have logs := service_log layout configuration positive serviceFits
  unfold BLSReply.Layouts.cacheLogs BLSReply.Layouts.records BLSRecord.Layouts.transcript at *
  simp only [logs]
  rfl

def storedView (value : (service layout configuration positive serviceFits).store.Value) :
    configuration.Value × Store layout :=
  (⟨value.val.1, value.property.1⟩,
    ⟨value.val.2, by
      have valid := value.property.2
      change (service layout configuration positive serviceFits).cacheLogs.valid value.val.2 at valid
      rw [service_cacheLogs] at valid
      exact valid⟩)

theorem stored_bytes (value : (service layout configuration positive serviceFits).store.Value)
    (fits : configuration.representation.encoding.words + (BLSExtractorFrame.store layout).representation.encoding.words < 2 ^ w) :
    (configuration.representation.prod (BLSExtractorFrame.store layout).representation fits).encoding.encode
        (storedView layout configuration positive serviceFits value) =
      (service layout configuration positive serviceFits).store.representation.encoding.encode value := by
  have logs := service_cacheLogs layout configuration positive serviceFits
  change configuration.representation.encoding.encode ⟨value.val.1, value.property.1⟩ ++
    (BLSExtractorFrame.store layout).representation.encoding.encode _ =
      configuration.representation.encoding.encode ⟨value.val.1, value.property.1⟩ ++
        (service layout configuration positive serviceFits).cacheLogs.representation.encoding.encode _
  congr 1
  have equal_bytes {A : Type} {left right : Layout w A} (equal : left = right)
      (x : left.Value) (y : right.Value) (same : x.val = y.val) :
      left.representation.encoding.encode x = right.representation.encoding.encode y := by
    subst right
    cases Subtype.ext same
    rfl
  exact (equal_bytes logs _ _ rfl).symm

theorem extraction_ready {fuel : Nat} {before after : (service layout configuration positive serviceFits).store.Value}
    (post : BLSCaller.Postcondition (service layout configuration positive serviceFits) fuel before after)
    (room : before.val.2.1.length + before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1 ≤
      layout.rows.accumulation.cache.capacityPred + 1)
    (forgery : Forgery layout) :
    BLSExtractorFrame.ready layout
      (extractInput layout (forgery, storedView layout configuration positive serviceFits after)) := by
  have available := post.extraction_room room
  change after.val.2.1.length + (after.val.2.2.1.length + after.val.2.2.2.length + 1) ≤
    layout.rows.accumulation.cache.capacityPred + 1 at available
  change after.val.2.1.length + after.val.2.2.1.length + after.val.2.2.2.length + 1 ≤ _
  omega

variable {P : Type} (pending : Representation w P)
    (fits : 1 + max (BLSExtractorFrame.forgery layout).representation.encoding.words pending.encoding.words +
      configuration.representation.encoding.words + (BLSExtractorFrame.store layout).representation.encoding.words < 2 ^ w)

include fits in
theorem caller_fits : 1 + max (BLSExtractorFrame.forgery layout).representation.encoding.words pending.encoding.words +
    (service layout configuration positive serviceFits).store.representation.encoding.words < 2 ^ w := by
  have sizes := congrArg (fun stored => stored.representation.encoding.words) (service_cacheLogs layout configuration positive serviceFits)
  change 1 + max _ _ + (configuration.representation.encoding.words +
    (service layout configuration positive serviceFits).cacheLogs.representation.encoding.words) < _
  rw [sizes]
  omega

def callerOutput : Representation w ((Forgery layout ⊕ P) × (service layout configuration positive serviceFits).store.Value) :=
  ((BLSExtractorFrame.forgery layout).representation.sum pending (width_pos layout.rows.accumulation.cache.wordFits) (by omega)).prod
    (service layout configuration positive serviceFits).store.representation (caller_fits layout configuration positive serviceFits pending fits)

def packetView (value : (Forgery layout ⊕ P) × (service layout configuration positive serviceFits).store.Value) :
    Packet (P := P) (C := configuration.Value) layout :=
  (value.1, storedView layout configuration positive serviceFits value.2)

theorem packet_bytes (value : (Forgery layout ⊕ P) × (service layout configuration positive serviceFits).store.Value) :
    (input layout configuration.representation pending fits).encoding.encode
        (packetView layout configuration positive serviceFits value) =
      (callerOutput layout configuration positive serviceFits pending fits).encoding.encode value := by
  have bytes := stored_bytes layout configuration positive serviceFits value.2 (by omega)
  change _ ++ _ = _ ++ _
  exact congrArg (fun stored =>
    (((BLSExtractorFrame.forgery layout).representation.sum pending (width_pos layout.rows.accumulation.cache.wordFits)
      (by omega)).encoding.encode value.1) ++ stored) bytes

theorem packet_ready {fuel : Nat} {before after : (service layout configuration positive serviceFits).store.Value}
    (post : BLSCaller.Postcondition (service layout configuration positive serviceFits) fuel before after)
    (room : before.val.2.1.length + before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1 ≤
      layout.rows.accumulation.cache.capacityPred + 1)
    (head : Forgery layout ⊕ P) :
    ready layout (BLSExtractorFrame.ready layout)
      (packetView layout configuration positive serviceFits (head, after)) := by
  cases head with
  | inl forgery => exact extraction_ready layout configuration positive serviceFits post room forgery
  | inr pending => trivial

theorem packet_signature_ready {fuel : Nat} {before after : (service layout configuration positive serviceFits).store.Value}
    (post : BLSCaller.Postcondition (service layout configuration positive serviceFits) fuel before after)
    (room : before.val.2.1.length + before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1 ≤
      layout.rows.accumulation.cache.capacityPred + 1)
    (head : Forgery layout ⊕ P) :
    ready layout (BLSExtractorFrame.signatureReady layout)
      (packetView layout configuration positive serviceFits (head, after)) := by
  cases head with
  | inl forgery =>
    exact BLSExtractorFrame.signatureReady_of_ready layout _
      (extraction_ready layout configuration positive serviceFits post room forgery)
  | inr pending => trivial

end Signatures.Runtime.CaliperBackend.BLSCallerFinish
