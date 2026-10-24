import Proofs.Runtime.Caliper.WeightedHashBounds
import Proofs.Runtime.Caliper.WeightedSignBounds
import Proofs.Runtime.Caliper.UniformQuery

/-! A shared private store for weighted random/hash/sign service. Both reply
programs use the same cache, encodings and independently bounded reply logs. -/
namespace Signatures.Runtime.CaliperBackend.WeightedOracle
open Caliper BoundedSource

structure Layouts (w : Nat) (K M F R C G : Type) where
  evaluation : CacheAccumulate.Layouts w K F R
  zero : evaluation.cache.value.Value
  default : evaluation.cache.value.Value
  message : Layout w M
  config : Layout w C
  point : Layout w G
  hashCapacityPred : Nat
  signCapacityPred : Nat
  hashCountFits : hashCapacityPred + 1 < 2 ^ w
  signCountFits : signCapacityPred + 1 < 2 ^ w
  storageFits : 32 * (evaluation.cache.key.representation.encoding.words +
    message.representation.encoding.words + config.representation.encoding.words +
    point.representation.encoding.words + evaluation.cache.value.representation.encoding.words +
    evaluation.cache.lookup.table.representation.encoding.words +
    (1 + (hashCapacityPred + 1) * (evaluation.cache.key.representation.encoding.words + point.representation.encoding.words)) +
    (1 + (signCapacityPred + 1) * (message.representation.encoding.words + point.representation.encoding.words))) < 2 ^ w

namespace Layouts
variable {w : Nat} {K M F R C G : Type} (layout : Layouts w K M F R C G)
def signing : WeightedSign.Layouts w K M F R C G where
  evaluation := layout.evaluation
  message := layout.message
  config := layout.config
  point := layout.point
  hashCapacity := layout.hashCapacityPred + 1
  signCapacityPred := layout.signCapacityPred
  hashCountFits := layout.hashCountFits
  signCountFits := layout.signCountFits
  storageFits := layout.storageFits
def hashing : WeightedHash.Layouts w K M R C G where
  cache := layout.evaluation.cache
  default := layout.default
  message := layout.message
  config := layout.config
  point := layout.point
  hashCapacityPred := layout.hashCapacityPred
  signCapacity := layout.signCapacityPred + 1
  hashCountFits := layout.hashCountFits
  signCountFits := layout.signCountFits
  storageFits := layout.storageFits
abbrev store := layout.signing.store
abbrev groupOutput := layout.signing.output
abbrev responseInput := layout.signing.responseInput
def width : Nat := layout.signing.width
theorem hashStore : layout.hashing.store = layout.store := rfl
theorem hashOutput : layout.hashing.output = layout.groupOutput := rfl
theorem hashResponse : layout.hashing.responseInput = layout.responseInput := rfl
theorem tagFits {words : Nat} (bound : words ≤ 4 + 4 * layout.width) : words < 2 ^ w := by
  have lower : 1 ≤ layout.width := by
    unfold width WeightedSign.Layouts.width WeightedSign.Layouts.hashWords WeightedSign.Layouts.signWords
    omega
  have capacity : 32 * layout.width < 2 ^ w := layout.storageFits
  exact (bound.trans (by omega)).trans_lt capacity
theorem store_le : layout.store.representation.encoding.words ≤ layout.width := by
  change _ + (_ + (layout.signing.hashWords + layout.signing.signWords)) ≤ _
  unfold width WeightedSign.Layouts.width
  omega
theorem groupOutput_le : layout.groupOutput.representation.encoding.words ≤ layout.width := by
  change _ + (_ + (_ + (layout.signing.hashWords + layout.signing.signWords))) ≤ _
  unfold width WeightedSign.Layouts.width
  omega

variable [DecidableEq K]
def groupInput := layout.hashing.input.representation.sum layout.signing.input.representation
  (width_pos layout.evaluation.cache.wordFits) (layout.tagFits (by
    change 1 + max (_ + (_ + (_ + (layout.signing.hashWords + layout.signing.signWords))))
      (_ + (_ + (_ + (layout.signing.hashWords + layout.signing.signWords)))) ≤ _
    unfold width WeightedSign.Layouts.width
    dsimp only [hashing, signing]
    omega))
theorem hashInput_le : layout.hashing.input.representation.encoding.words ≤ layout.width := by
  change _ + (_ + (_ + (layout.signing.hashWords + layout.signing.signWords))) ≤ _
  unfold width WeightedSign.Layouts.width
  dsimp only [hashing, signing]
  omega
omit [DecidableEq K] in
theorem signInput_le : layout.signing.input.representation.encoding.words ≤ layout.width := by
  change _ + (_ + (_ + (layout.signing.hashWords + layout.signing.signWords))) ≤ _
  unfold width WeightedSign.Layouts.width
  omega
theorem groupInput_le : layout.groupInput.encoding.words ≤ 1 + layout.width := by
  have left := layout.hashInput_le
  have right := layout.signInput_le
  change 1 + max _ _ ≤ _
  omega

variable (randomBound : Nat) (randomFits : randomBound + 1 ≤ 2 ^ w)
def randomInput := UniformQuery.input randomBound layout.evaluation.cache.wordFits randomFits
  layout.store.representation (layout.tagFits (by have := layout.store_le; omega))
def randomOutput := UniformQuery.output randomBound layout.evaluation.cache.wordFits randomFits
  layout.store.representation (layout.tagFits (by have := layout.store_le; omega))
def input := (layout.randomInput randomBound randomFits).sum layout.groupInput
  (width_pos layout.evaluation.cache.wordFits) (layout.tagFits (by
    have stored := layout.store_le
    have groups := layout.groupInput_le
    change 1 + max (1 + layout.store.representation.encoding.words) layout.groupInput.encoding.words ≤ _
    omega))
def output := (layout.randomOutput randomBound randomFits).sum layout.groupOutput.representation
  (width_pos layout.evaluation.cache.wordFits) (layout.tagFits (by
    have stored := layout.store_le
    have groups := layout.groupOutput_le
    change 1 + max (2 + layout.store.representation.encoding.words) layout.groupOutput.representation.encoding.words ≤ _
    omega))
def randomTag : Realizer .unit (layout.randomOutput randomBound randomFits)
    (layout.output randomBound randomFits) Sum.inl :=
  inlRealizer .unit (by decide) _ _ layout.evaluation.cache.wordFits (layout.output randomBound randomFits).fits
def groupTag : Realizer .unit layout.groupOutput.representation
    (layout.output randomBound randomFits) Sum.inr :=
  inrRealizer .unit (by decide) _ _ layout.evaluation.cache.wordFits (layout.output randomBound randomFits).fits

end Layouts

abbrev GroupInput {w : Nat} {K M F R C G : Type} [DecidableEq K] (layout : Layouts w K M F R C G) :=
  layout.hashing.input.Value ⊕ layout.signing.input.Value
abbrev Input {w : Nat} {K M F R C G : Type} [DecidableEq K] (layout : Layouts w K M F R C G) (randomBound : Nat) :=
  (Fin (randomBound + 1) × layout.store.Value) ⊕ GroupInput layout
abbrev Output {w : Nat} {K M F R C G : Type} (layout : Layouts w K M F R C G) (randomBound : Nat) :=
  (UniformQuery.Reply randomBound × layout.store.Value) ⊕ layout.groupOutput.Value

end Signatures.Runtime.CaliperBackend.WeightedOracle
