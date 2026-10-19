import Signatures.Runtime.Caliper.BLSOracleReady
import Signatures.Runtime.Caliper.SumContextMerge

/-! Actual packet conversion between the generic caller and the BLS service.
Queries and replies use independent bounded representations; the private store
is separate. Readiness proofs change no bytes. All tag/padding/context movement
is performed by the generated local code. -/

namespace Signatures.Runtime.CaliperBackend.BLSCallerPackets
open Caliper BoundedSource

variable {w : Nat} {M R C G : Type} [DecidableEq M]
    (layout : BLSReply.Layouts w M R C G) (default : layout.cache.value.Value)

omit [DecidableEq M] in
theorem requestFits : 2 + layout.cache.key.representation.encoding.words +
    layout.store.representation.encoding.words < 2 ^ w := by
  have room := layout.storageFits
  have store := BLSOracle.store_le layout
  have key : layout.cache.key.representation.encoding.words ≤ layout.width := by
    dsimp only [BLSReply.Layouts.width]
    rw [BLSReply.Layouts.lookup_width]
    omega
  change 16 * layout.width < 2 ^ w at room
  have positive : 0 < layout.width := by
    dsimp only [BLSReply.Layouts.width, BLSReply.Layouts.logWords]
    omega
  omega

def groupRequest : Representation w (layout.cache.key.Value ⊕ layout.cache.key.Value) :=
  layout.cache.key.representation.sum layout.cache.key.representation (width_pos layout.cache.wordFits)
    (by have := requestFits layout; omega)

def groupInput : Representation w ((layout.cache.key.Value ⊕ layout.cache.key.Value) × layout.store.Value) :=
  (groupRequest layout).prod layout.store.representation (by
    have := requestFits layout
    change (1 + max _ _) + _ < _
    omega)

def groupOutput := SumContext.output layout.cache.key.representation layout.cache.key.representation
  layout.store.representation layout.cache.wordFits (groupInput layout).fits

variable (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)

abbrev Request := Fin (randomBound + 1) ⊕ (layout.cache.key.Value ⊕ layout.cache.key.Value)
abbrev Reply := UniformQuery.Reply randomBound ⊕ layout.point.Value
abbrev Packet := Request layout randomBound × layout.store.Value
abbrev Raw := (Fin (randomBound + 1) × layout.store.Value) ⊕
  ((layout.cache.key.Value × layout.store.Value) ⊕ (layout.cache.key.Value × layout.store.Value))

def request : Representation w (Request layout randomBound) :=
  (UniformQuery.port randomBound layout.cache.wordFits randomFits).request.sum (groupRequest layout)
    (width_pos layout.cache.wordFits) (by
      have := requestFits layout
      change 1 + max 1 (1 + max layout.cache.key.representation.encoding.words layout.cache.key.representation.encoding.words) < 2 ^ w
      omega)

def input : Representation w (Packet layout randomBound) :=
  (request layout randomBound randomFits).prod layout.store.representation (by
    have := requestFits layout
    change 1 + max 1 (1 + max layout.cache.key.representation.encoding.words layout.cache.key.representation.encoding.words) + _ < 2 ^ w
    omega)

def raw : Representation w (Raw layout randomBound) :=
  (BLSOracle.randomInput layout randomBound randomFits).sum (groupOutput layout) (width_pos layout.cache.wordFits) (by
    have := requestFits layout
    change 1 + max (1 + layout.store.representation.encoding.words)
      (1 + max (layout.cache.key.representation.encoding.words + layout.store.representation.encoding.words)
        (layout.cache.key.representation.encoding.words + layout.store.representation.encoding.words)) < 2 ^ w
    omega)

def prepared (value : Packet layout randomBound) : Raw layout randomBound :=
  match value.1 with
  | .inl n => .inl (n, value.2)
  | .inr (.inl message) => .inr (.inl (message, value.2))
  | .inr (.inr message) => .inr (.inr (message, value.2))

def prepare : Realizer .unit (input layout randomBound randomFits) (raw layout randomBound randomFits) (prepared layout randomBound) :=
  ((SumContext.distribute (UniformQuery.port randomBound layout.cache.wordFits randomFits).request
    (groupRequest layout) layout.store.representation layout.cache.wordFits (input layout randomBound randomFits).fits).then
      (branchRealizer .unit (by decide) (BLSOracle.randomInput layout randomBound randomFits) (groupInput layout)
        (raw layout randomBound randomFits)
        (inlRealizer .unit (by decide) (BLSOracle.randomInput layout randomBound randomFits) (groupOutput layout)
          layout.cache.wordFits (raw layout randomBound randomFits).fits)
        ((SumContext.distribute layout.cache.key.representation layout.cache.key.representation layout.store.representation
          layout.cache.wordFits (groupInput layout).fits).then
            (inrRealizer .unit (by decide) (BLSOracle.randomInput layout randomBound randomFits) (groupOutput layout)
              layout.cache.wordFits (raw layout randomBound randomFits).fits))
        layout.cache.wordFits (by
          have := requestFits layout
          change 1 + max (1 + layout.store.representation.encoding.words)
            ((1 + max layout.cache.key.representation.encoding.words layout.cache.key.representation.encoding.words) +
              layout.store.representation.encoding.words) < 2 ^ w
          omega))).viewOutput (raw layout randomBound randomFits) (prepared layout randomBound) (by
            intro value
            rcases value with ⟨n | (message | message), saved⟩ <;> rfl)

def ready (value : Packet layout randomBound) : Prop :=
  match value.1 with
  | .inl _ => True
  | .inr (.inl message) => layout.guard default.val false (message.val, value.2.val)
  | .inr (.inr message) => layout.guard default.val true (message.val, value.2.val)

instance : DecidablePred (ready layout default randomBound) := fun value => by
  rcases value with ⟨n | (message | message), saved⟩ <;> dsimp [ready] <;> infer_instance

/-- Erase only proof packaging after `prepare` has built the service bytes. -/
def serviceRequest (value : Packet layout randomBound) (valid : ready layout default randomBound value) :
    (Fin (randomBound + 1) × layout.store.Value) ⊕ (BLSDispatch.input layout default).Value :=
  match value with
  | (.inl n, saved) => .inl (n, saved)
  | (.inr (.inl message), saved) => .inr (BLSDispatch.request layout default false
      ⟨(message.val, saved.val), ⟨message.property, saved.property⟩, valid⟩)
  | (.inr (.inr message), saved) => .inr (BLSDispatch.request layout default true
      ⟨(message.val, saved.val), ⟨message.property, saved.property⟩, valid⟩)

theorem request_bytes (value : Packet layout randomBound) (valid : ready layout default randomBound value) :
    (BLSOracle.input layout default randomBound randomFits).encoding.encode (serviceRequest layout default randomBound value valid) =
      (raw layout randomBound randomFits).encoding.encode (prepared layout randomBound value) := by
  rcases value with ⟨n | (message | message), saved⟩ <;> rfl

def reply : Representation w (Reply layout randomBound) :=
  (UniformQuery.port randomBound layout.cache.wordFits randomFits).reply.sum layout.point.representation
    (width_pos layout.cache.wordFits) (by
      have := BLSOracle.outputFits layout randomBound randomFits
      change 1 + max 2 layout.point.representation.encoding.words < 2 ^ w
      change 1 + max (2 + layout.store.representation.encoding.words)
        (layout.point.representation.encoding.words + layout.store.representation.encoding.words) < 2 ^ w at this
      omega)

def output : Representation w (Reply layout randomBound × layout.store.Value) :=
  (reply layout randomBound randomFits).prod layout.store.representation (by
    have := BLSOracle.outputFits layout randomBound randomFits
    change 1 + max 2 layout.point.representation.encoding.words + layout.store.representation.encoding.words < 2 ^ w
    change 1 + max (2 + layout.store.representation.encoding.words)
      (layout.point.representation.encoding.words + layout.store.representation.encoding.words) < 2 ^ w at this
    omega)

def finished : (UniformQuery.Reply randomBound × layout.store.Value) ⊕ layout.output.Value →
    Reply layout randomBound × layout.store.Value
  | .inl value => (.inl value.1, value.2)
  | .inr value => (.inr (productView layout.point layout.store value).1, (productView layout.point layout.store value).2)

def finish : Realizer .unit (BLSOracle.output layout randomBound randomFits) (output layout randomBound randomFits)
    (finished layout randomBound) :=
  ((SumContext.merge (UniformQuery.port randomBound layout.cache.wordFits randomFits).reply layout.point.representation
    layout.store.representation layout.cache.wordFits (output layout randomBound randomFits).fits).viewInput
      (BLSOracle.output layout randomBound randomFits) (Sum.map id (productView layout.point layout.store)) (by
        intro value
        cases value <;> rfl)).viewOutput (output layout randomBound randomFits) (finished layout randomBound) (by
          intro value
          cases value <;> rfl)

end Signatures.Runtime.CaliperBackend.BLSCallerPackets
