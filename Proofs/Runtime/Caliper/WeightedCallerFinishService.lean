import Proofs.Runtime.Caliper.WeightedCallerFinish
import Proofs.Runtime.Caliper.WeightedCallerPostcondition

/-! A caller service and extractor share their cache, token encodings and log
capacity. Configuration is an additional bounded stored value. The bridge to
the terminal frame changes only equal-byte mathematical product views; the
actual removal of configuration and union padding remains executed routing. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerFinish
open Caliper BoundedSource
variable {w : Nat} {K M G F R C : Type}

def serviceWidth (layout : WeightedExtractor.Layouts w K M G F R) (configuration : Layout w C) : Nat :=
  layout.signing.rows.accumulation.cache.key.representation.encoding.words +
    layout.message.representation.encoding.words + configuration.representation.encoding.words +
    layout.signing.rows.point.representation.encoding.words +
    layout.signing.rows.accumulation.cache.value.representation.encoding.words +
    layout.table.representation.encoding.words + layout.hashTokens.representation.encoding.words +
    layout.signTokens.representation.encoding.words

variable (layout : WeightedExtractor.Layouts w K M G F R) (configuration : Layout w C)
    (zero default : layout.signing.rows.accumulation.cache.value.Value)
    (hashPositive : 0 < layout.hashCapacity) (signPositive : 0 < layout.signing.capacity)
    (serviceFits : 32 * serviceWidth layout configuration < 2 ^ w)

def service : WeightedOracle.Layouts w K M F R C G where
  evaluation := layout.signing.rows.accumulation
  zero := zero
  default := default
  message := layout.message
  config := configuration
  point := layout.signing.rows.point
  hashCapacityPred := layout.hashCapacity - 1
  signCapacityPred := layout.signing.capacity - 1
  hashCountFits := by have := layout.hashCounterFits; omega
  signCountFits := by have := layout.signing.counterFits; omega
  storageFits := by
    simp only [Nat.sub_add_cancel hashPositive, Nat.sub_add_cancel signPositive]
    exact serviceFits

theorem service_hashLog : (service layout configuration zero default hashPositive signPositive serviceFits).signing.hashLog =
    layout.hashTokens := by
  unfold WeightedSign.Layouts.hashLog
  dsimp only [service, WeightedOracle.Layouts.signing]
  simp only [Nat.sub_add_cancel hashPositive]
  rfl
theorem service_signLog : (service layout configuration zero default hashPositive signPositive serviceFits).signing.signLog =
    layout.signTokens := by
  unfold WeightedSign.Layouts.signLog WeightedRecord.Layouts.log
  dsimp only [service, WeightedOracle.Layouts.signing, WeightedSign.Layouts.recorder]
  simp only [Nat.sub_add_cancel signPositive]
  rfl
theorem service_logs : (service layout configuration zero default hashPositive signPositive serviceFits).signing.logs = layout.logs := by
  change ((service layout configuration zero default hashPositive signPositive serviceFits).signing.hashLog.prod
    (service layout configuration zero default hashPositive signPositive serviceFits).signing.signLog _) = _
  simp only [service_hashLog, service_signLog]
  rfl
theorem service_cacheLogs : (service layout configuration zero default hashPositive signPositive serviceFits).signing.cacheLogs = layout.store := by
  change (layout.table.prod (service layout configuration zero default hashPositive signPositive serviceFits).signing.logs _) = _
  simp only [service_logs]
  rfl

def storedView (value : (service layout configuration zero default hashPositive signPositive serviceFits).store.Value) :
    configuration.Value × Store layout :=
  (⟨value.val.1, value.property.1⟩,
    ⟨value.val.2, by
      have valid := value.property.2
      change (service layout configuration zero default hashPositive signPositive serviceFits).signing.cacheLogs.valid value.val.2 at valid
      rw [service_cacheLogs] at valid
      exact valid⟩)

theorem stored_bytes (value : (service layout configuration zero default hashPositive signPositive serviceFits).store.Value)
    (fits : configuration.representation.encoding.words + layout.store.representation.encoding.words < 2 ^ w) :
    (configuration.representation.prod layout.store.representation fits).encoding.encode
        (storedView layout configuration zero default hashPositive signPositive serviceFits value) =
      (service layout configuration zero default hashPositive signPositive serviceFits).store.representation.encoding.encode value := by
  have logs := service_cacheLogs layout configuration zero default hashPositive signPositive serviceFits
  change configuration.representation.encoding.encode ⟨value.val.1, value.property.1⟩ ++
    layout.store.representation.encoding.encode _ =
      configuration.representation.encoding.encode ⟨value.val.1, value.property.1⟩ ++
        (service layout configuration zero default hashPositive signPositive serviceFits).signing.cacheLogs.representation.encoding.encode _
  congr 1
  have equal_bytes {A : Type} {left right : Layout w A} (equal : left = right)
      (x : left.Value) (y : right.Value) (same : x.val = y.val) :
      left.representation.encoding.encode x = right.representation.encoding.encode y := by
    subst right
    cases Subtype.ext same
    rfl
  exact (equal_bytes logs _ _ rfl).symm

theorem extraction_ready {fuel : Nat} {before after : (service layout configuration zero default hashPositive signPositive serviceFits).store.Value}
    (post : WeightedCaller.Postcondition (service layout configuration zero default hashPositive signPositive serviceFits) layout.signing.terms fuel before after)
    (room : before.val.2.1.length + max 1 layout.signing.terms *
      (before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1) ≤
      layout.signing.rows.accumulation.cache.capacityPred + 1)
    (forgery : Forgery layout) :
    layout.ready
      (extractInput layout (forgery, storedView layout configuration zero default hashPositive signPositive serviceFits after)) := by
  have available := post.extraction_room room
  have hashBound := Nat.mul_le_mul_right after.val.2.2.1.length (Nat.le_max_left 1 layout.signing.terms)
  have signBound := Nat.mul_le_mul_right after.val.2.2.2.length (Nat.le_max_right 1 layout.signing.terms)
  have targetBound := Nat.le_max_right 1 layout.signing.terms
  change after.val.2.1.length + max 1 layout.signing.terms *
    (after.val.2.2.1.length + after.val.2.2.2.length + 1) ≤ layout.signing.rows.accumulation.cache.capacityPred + 1 at available
  change after.val.2.1.length + after.val.2.2.1.length +
    layout.signing.terms * after.val.2.2.2.length + layout.signing.terms ≤ _
  simp only [Nat.mul_add, Nat.mul_one, Nat.one_mul] at available hashBound
  omega

variable {P : Type} (pending : Representation w P)
    (fits : 1 + max layout.forgery.representation.encoding.words pending.encoding.words +
      configuration.representation.encoding.words + layout.store.representation.encoding.words < 2 ^ w)

include fits in
theorem caller_fits : 1 + max layout.forgery.representation.encoding.words pending.encoding.words +
    (service layout configuration zero default hashPositive signPositive serviceFits).store.representation.encoding.words < 2 ^ w := by
  have sizes := congrArg (fun stored => stored.representation.encoding.words) (service_cacheLogs layout configuration zero default hashPositive signPositive serviceFits)
  change 1 + max _ _ + (configuration.representation.encoding.words +
    (service layout configuration zero default hashPositive signPositive serviceFits).signing.cacheLogs.representation.encoding.words) < _
  rw [sizes]
  omega

def callerOutput : Representation w ((Forgery layout ⊕ P) × (service layout configuration zero default hashPositive signPositive serviceFits).store.Value) :=
  (layout.forgery.representation.sum pending (width_pos layout.signing.rows.accumulation.cache.wordFits) (by omega)).prod
    (service layout configuration zero default hashPositive signPositive serviceFits).store.representation (caller_fits layout configuration zero default hashPositive signPositive serviceFits pending fits)

def packetView (value : (Forgery layout ⊕ P) × (service layout configuration zero default hashPositive signPositive serviceFits).store.Value) :
    Packet (P := P) (C := configuration.Value) layout :=
  (value.1, storedView layout configuration zero default hashPositive signPositive serviceFits value.2)

theorem packet_bytes (value : (Forgery layout ⊕ P) × (service layout configuration zero default hashPositive signPositive serviceFits).store.Value) :
    (input layout configuration.representation pending fits).encoding.encode
        (packetView layout configuration zero default hashPositive signPositive serviceFits value) =
      (callerOutput layout configuration zero default hashPositive signPositive serviceFits pending fits).encoding.encode value := by
  have bytes := stored_bytes layout configuration zero default hashPositive signPositive serviceFits value.2 (by omega)
  change _ ++ _ = _ ++ _
  exact congrArg (fun stored =>
    ((layout.forgery.representation.sum pending (width_pos layout.signing.rows.accumulation.cache.wordFits)
      (by omega)).encoding.encode value.1) ++ stored) bytes

theorem packet_ready {fuel : Nat} {before after : (service layout configuration zero default hashPositive signPositive serviceFits).store.Value}
    (post : WeightedCaller.Postcondition (service layout configuration zero default hashPositive signPositive serviceFits) layout.signing.terms fuel before after)
    (room : before.val.2.1.length + max 1 layout.signing.terms *
      (before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1) ≤
      layout.signing.rows.accumulation.cache.capacityPred + 1)
    (head : Forgery layout ⊕ P) :
    ready layout (layout.ready)
      (packetView layout configuration zero default hashPositive signPositive serviceFits (head, after)) := by
  cases head with
  | inl forgery => exact extraction_ready layout configuration zero default hashPositive signPositive serviceFits post room forgery
  | inr pending => trivial

theorem packet_badReady {fuel : Nat} {before after : (service layout configuration zero default hashPositive signPositive serviceFits).store.Value}
    (post : WeightedCaller.Postcondition (service layout configuration zero default hashPositive signPositive serviceFits) layout.signing.terms fuel before after)
    (room : before.val.2.1.length + max 1 layout.signing.terms *
      (before.val.2.2.1.length + before.val.2.2.2.length + 2 * fuel + 1) ≤
      layout.signing.rows.accumulation.cache.capacityPred + 1)
    (head : Forgery layout ⊕ P) :
    ready layout (layout.badReady)
      (packetView layout configuration zero default hashPositive signPositive serviceFits (head, after)) := by
  cases head with
  | inl forgery =>
    have good := extraction_ready layout configuration zero default hashPositive signPositive serviceFits post room forgery
    change after.val.2.1.length + layout.signing.terms * after.val.2.2.2.length + layout.signing.terms ≤ _
    change after.val.2.1.length + after.val.2.2.1.length +
      layout.signing.terms * after.val.2.2.2.length + layout.signing.terms ≤ _ at good
    omega
  | inr pending => trivial

end Signatures.Runtime.CaliperBackend.WeightedCallerFinish
