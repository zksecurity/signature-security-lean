import Signatures.Runtime.Caliper.WeightedInitialization
import Signatures.Runtime.Caliper.PairBounds

/-! Executed challenge setup for a weighted reduction. The configuration and
public key are runtime inputs; the unused key generator remains part of the
standard DLog challenge. The cache and both logs are initialized explicitly.
This construction is independent of the index/message types and capacities. -/
namespace Signatures.Runtime.CaliperBackend.WeightedSetup
open Caliper BoundedSource

variable {w : Nat} {K M F R C G PK : Type}

structure Layouts (service : WeightedOracle.Layouts w K M F R C G) (PK : Type) where
  key : Layout w PK
  storageFits : 16 * (service.store.representation.encoding.words +
    service.config.representation.encoding.words + 2 * key.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {service : WeightedOracle.Layouts w K M F R C G} (layout : Layouts service PK)
def width : Nat := service.store.representation.encoding.words +
  service.config.representation.encoding.words + 2 * layout.key.representation.encoding.words
theorem fits {n : Nat} (bound : n ≤ 16 * layout.width) : n < 2 ^ w :=
  bound.trans_lt layout.storageFits
def keys : Layout w (PK × PK) := layout.key.prod layout.key (layout.fits (by unfold width; omega))
def challenge : Layout w (C × (PK × PK)) :=
  service.config.prod layout.keys (layout.fits (by change _ + (_ + _) ≤ _; unfold width; omega))
theorem outputFits : layout.key.representation.encoding.words + service.store.representation.encoding.words < 2 ^ w :=
  layout.fits (by unfold width; omega)
def prepared := WeightedInitialization.sourceInput service layout.key layout.outputFits
def output := WeightedInitialization.sourceOutput service layout.key layout.outputFits
def callerInput := layout.key.representation.prod service.store.representation layout.outputFits
def start (value : layout.challenge.Value) : layout.key.Value × service.store.Value :=
  (⟨value.val.2.2, value.property.2.2⟩, WeightedInitialization.store service ⟨value.val.1, value.property.1⟩)
def result (value : layout.challenge.Value) : layout.output.Value :=
  ⟨(value.val.2.2, value.val.1, [], [], []), value.property.2.2, value.property.1,
    (WeightedInitialization.empty service).property⟩
def view (value : layout.output.Value) : layout.key.Value × service.store.Value :=
  productView layout.key service.store value
theorem view_result (value : layout.challenge.Value) : layout.view (layout.result value) = layout.start value := rfl
theorem view_bytes (value : layout.output.Value) :
    layout.callerInput.encoding.encode (layout.view value) = layout.output.representation.encoding.encode value := rfl
theorem sizes :
    layout.key.representation.encoding.words ≤ layout.width ∧
    service.config.representation.encoding.words ≤ layout.width ∧
    layout.challenge.representation.encoding.words ≤ layout.width ∧
    layout.output.representation.encoding.words ≤ layout.width := by
  change _ ∧ _ ∧ (_ + (_ + _)) ≤ _ ∧ (_ + _) ≤ _
  unfold width
  omega
end Layouts

variable {service : WeightedOracle.Layouts w K M F R C G} (layout : Layouts service PK)

def config : Implementation .unit layout.challenge service.config Prod.fst :=
  Implementation.first (by decide) _ _ service.evaluation.cache.wordFits _
def keys : Implementation .unit layout.challenge layout.keys Prod.snd :=
  Implementation.second (by decide) _ _ service.evaluation.cache.wordFits _
def publicKey : Implementation .unit layout.challenge layout.key (fun value => value.2.2) :=
  (keys layout).then (Implementation.second (by decide) _ _ service.evaluation.cache.wordFits _)
theorem config_buffers : (config layout).program.code.memBound ≤ 2 :=
  Implementation.first_buffers _ _ _ _ _
theorem publicKey_buffers : (publicKey layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)
def prepared : Implementation .unit layout.challenge layout.prepared (fun value => (value.2.2, value.1)) :=
  (publicKey layout).pair (config layout) (by decide) service.evaluation.cache.wordFits
    (CacheAccumulate.nameFits service.evaluation _ (publicKey_buffers layout) (by have := service.evaluation.cache.wordFits; omega))
    (CacheAccumulate.nameFits service.evaluation _ (config_buffers layout) (by have := service.evaluation.cache.wordFits; omega))
    (layout.fits (by have := layout.sizes; omega))
    (layout.fits (by have := layout.sizes; omega)) _
def implementation : Implementation .unit layout.challenge layout.output
    (fun value => (value.2.2, value.1, [], [], [])) :=
  (prepared layout).then (WeightedInitialization.implementation service layout.key layout.outputFits)
def realizer : Realizer .unit layout.challenge.representation layout.callerInput layout.start :=
  (implementation layout).program.viewOutput layout.callerInput layout.start
    (fun _ => rfl)

theorem bounded : (implementation layout).BoundedBy (200 * layout.width) (700 * layout.width + 250) := by
  have keyBound : (publicKey layout).BoundedBy
      (24 * layout.key.representation.encoding.words) (78 * layout.key.representation.encoding.words + 29) := by
    apply ((Implementation.second_boundedBy _ _ _ _).then (Implementation.second_boundedBy _ _ _ _)).mono
    all_goals simp only [Layout.prod_words]; omega
  have prefixBound : (prepared layout).BoundedBy (160 * layout.width) (600 * layout.width + 200) := by
    apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ keyBound (Implementation.first_boundedBy _ _ _ _)).mono
    all_goals have := layout.sizes; omega
  apply (prefixBound.then (WeightedInitialization.implementation_bounded service layout.key layout.outputFits)).mono
  all_goals have := layout.sizes; dsimp only [Layouts.output] at this; omega

theorem names : NamesAccounted (implementation layout).program.code 3 := by
  have keyNames : NamesAccounted (publicKey layout).program.code 3 :=
    (Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)
  exact (Implementation.pair_names _ _ _ _ _ _ _ _ keyNames (Implementation.first_names _ _ _ _ _)).seq
    (WeightedInitialization.implementation_names service layout.key layout.outputFits).accounted
theorem buffers : (implementation layout).program.code.memBound ≤ 3 :=
  max_le (Implementation.pair_buffers _ _ _ _ _ _ _ _ (publicKey_buffers layout) (config_buffers layout))
    ((WeightedInitialization.implementation_buffers service layout.key layout.outputFits).trans (by decide))
end Signatures.Runtime.CaliperBackend.WeightedSetup
