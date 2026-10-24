import Proofs.Runtime.Caliper.WeightedOracle
import Proofs.Runtime.Caliper.SumContextMerge

/-! Executed packet conversion for weighted callers. Hash indices and signing
messages keep their own layouts. Distribution and merging copy the private
store with charged instructions; readiness supplies only proof packaging. -/
namespace Signatures.Runtime.CaliperBackend.WeightedCallerPackets
open Caliper BoundedSource

variable {w : Nat} {K M F R C G : Type} (layout : WeightedOracle.Layouts w K M F R C G)

def width : Nat := 3 + layout.evaluation.cache.key.representation.encoding.words +
  layout.message.representation.encoding.words + layout.point.representation.encoding.words +
  layout.store.representation.encoding.words

theorem fits {words : Nat} (bound : words ≤ width layout) : words < 2 ^ w := by
  apply layout.tagFits
  have size : width layout ≤ 3 + layout.width := by
    unfold width
    change 3 + _ + _ + _ + (_ + (_ + (layout.signing.hashWords + layout.signing.signWords))) ≤ _
    unfold WeightedOracle.Layouts.width WeightedSign.Layouts.width
    dsimp only [WeightedOracle.Layouts.signing]
    omega
  omega

def groupRequest := layout.evaluation.cache.key.representation.sum layout.message.representation
  (width_pos layout.evaluation.cache.wordFits) (fits layout (by unfold width; omega))
def groupInput := (groupRequest layout).prod layout.store.representation
  (fits layout (by change (1 + max _ _) + _ ≤ _; unfold width; omega))
def groupOutput := SumContext.output layout.evaluation.cache.key.representation layout.message.representation
  layout.store.representation layout.evaluation.cache.wordFits (groupInput layout).fits

variable (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)

abbrev Request := Fin (randomBound + 1) ⊕ (layout.evaluation.cache.key.Value ⊕ layout.message.Value)
abbrev Reply := UniformQuery.Reply randomBound ⊕ layout.point.Value
abbrev Packet := Request layout randomBound × layout.store.Value
abbrev Raw := (Fin (randomBound + 1) × layout.store.Value) ⊕
  ((layout.evaluation.cache.key.Value × layout.store.Value) ⊕ (layout.message.Value × layout.store.Value))

def request : Representation w (Request layout randomBound) :=
  (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).request.sum (groupRequest layout)
    (width_pos layout.evaluation.cache.wordFits) (fits layout (by
      change 1 + max 1 (1 + max _ _) ≤ _
      unfold width; omega))
def input : Representation w (Packet layout randomBound) :=
  (request layout randomBound randomFits).prod layout.store.representation (fits layout (by
    change 1 + max 1 (1 + max _ _) + _ ≤ _
    unfold width; omega))
def raw : Representation w (Raw layout randomBound) :=
  (layout.randomInput randomBound randomFits).sum (groupOutput layout)
    (width_pos layout.evaluation.cache.wordFits) (fits layout (by
      change 1 + max (1 + layout.store.representation.encoding.words)
        (1 + max (layout.evaluation.cache.key.representation.encoding.words + layout.store.representation.encoding.words)
          (layout.message.representation.encoding.words + layout.store.representation.encoding.words)) ≤ _
      unfold width; omega))

def prepared (value : Packet layout randomBound) : Raw layout randomBound :=
  match value.1 with
  | .inl n => .inl (n, value.2)
  | .inr (.inl index) => .inr (.inl (index, value.2))
  | .inr (.inr message) => .inr (.inr (message, value.2))

def prepare : Realizer .unit (input layout randomBound randomFits) (raw layout randomBound randomFits)
    (prepared layout randomBound) :=
  ((SumContext.distribute (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).request
    (groupRequest layout) layout.store.representation layout.evaluation.cache.wordFits (input layout randomBound randomFits).fits).then
      (branchRealizer .unit (by decide) (layout.randomInput randomBound randomFits) (groupInput layout)
        (raw layout randomBound randomFits)
        (inlRealizer .unit (by decide) (layout.randomInput randomBound randomFits) (groupOutput layout)
          layout.evaluation.cache.wordFits (raw layout randomBound randomFits).fits)
        ((SumContext.distribute layout.evaluation.cache.key.representation layout.message.representation
          layout.store.representation layout.evaluation.cache.wordFits (groupInput layout).fits).then
            (inrRealizer .unit (by decide) (layout.randomInput randomBound randomFits) (groupOutput layout)
              layout.evaluation.cache.wordFits (raw layout randomBound randomFits).fits))
        layout.evaluation.cache.wordFits (fits layout (by
          change 1 + max (1 + layout.store.representation.encoding.words)
            ((1 + max layout.evaluation.cache.key.representation.encoding.words layout.message.representation.encoding.words) +
              layout.store.representation.encoding.words) ≤ _
          unfold width; omega)))).viewOutput (raw layout randomBound randomFits) (prepared layout randomBound) (by
            intro value
            rcases value with ⟨n | (index | message), saved⟩ <;> rfl)

def reply : Representation w (Reply layout randomBound) :=
  (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).reply.sum layout.point.representation
    (width_pos layout.evaluation.cache.wordFits) (fits layout (by change 1 + max 2 _ ≤ _; unfold width; omega))
def output : Representation w (Reply layout randomBound × layout.store.Value) :=
  (reply layout randomBound randomFits).prod layout.store.representation
    (fits layout (by change 1 + max 2 _ + _ ≤ _; unfold width; omega))

def finished : WeightedOracle.Output layout randomBound → Reply layout randomBound × layout.store.Value
  | .inl value => (.inl value.1, value.2)
  | .inr value => (.inr (productView layout.point layout.store value).1, (productView layout.point layout.store value).2)

def finish : Realizer .unit (layout.output randomBound randomFits) (output layout randomBound randomFits)
    (finished layout randomBound) :=
  ((SumContext.merge (UniformQuery.port randomBound layout.evaluation.cache.wordFits randomFits).reply
    layout.point.representation layout.store.representation layout.evaluation.cache.wordFits (output layout randomBound randomFits).fits).viewInput
      (layout.output randomBound randomFits) (Sum.map id (productView layout.point layout.store)) (by
        intro value
        cases value <;> rfl)).viewOutput (output layout randomBound randomFits) (finished layout randomBound) (by
          intro value
          cases value <;> rfl)

variable [DecidableEq K] (generate : M → List (K × F))

/-- A proof domain, not a host computation used by the executed converter.
The signing program itself generates and evaluates the terms. -/
def ready (value : Packet layout randomBound) : Prop :=
  match value.1 with
  | .inl _ => True
  | .inr (.inl index) => layout.hashing.room (index.val, value.2.val)
  | .inr (.inr message) => layout.signing.room (message.val, value.2.val) ∧
      value.2.val.2.1.length + (generate message.val).length ≤ layout.evaluation.cache.capacityPred + 1

instance : DecidablePred (ready layout randomBound generate) := fun value => by
  rcases value with ⟨n | (index | message), saved⟩ <;> dsimp [ready] <;> infer_instance

def serviceRequest (value : Packet layout randomBound) (valid : ready layout randomBound generate value) :
    WeightedOracle.Input layout randomBound :=
  match value with
  | (.inl n, saved) => .inl (n, saved)
  | (.inr (.inl index), saved) => .inr (.inl ⟨(index.val, saved.val), ⟨index.property, saved.property⟩, valid⟩)
  | (.inr (.inr message), saved) => .inr (.inr ⟨(message.val, saved.val), ⟨message.property, saved.property⟩, valid.1⟩)

theorem request_bytes (value : Packet layout randomBound) (valid : ready layout randomBound generate value) :
    (layout.input randomBound randomFits).encoding.encode (serviceRequest layout randomBound generate value valid) =
      (raw layout randomBound randomFits).encoding.encode (prepared layout randomBound value) := by
  rcases value with ⟨n | (index | message), saved⟩ <;> rfl

end Signatures.Runtime.CaliperBackend.WeightedCallerPackets
