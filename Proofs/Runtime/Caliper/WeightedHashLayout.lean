import Proofs.Runtime.Caliper.BLSCache
import Proofs.Runtime.Caliper.WeightedRecord
import Proofs.Runtime.Caliper.ByteRoute

/-! Frames for weighted hash queries. Hash indices and signing messages have
independent layouts and log capacities. A full private cache admits hits. -/
namespace Signatures.Runtime.CaliperBackend.WeightedHash
open Caliper BoundedSource

abbrev Store (K M R C G : Type) := C × (List (K × R) × Model.LazyAGM.Transcript K M G)
abbrev Request (K M R C G : Type) := K × Store K M R C G

structure Layouts (w : Nat) (K M R C G : Type) where
  cache : CacheLayout w K R
  default : cache.value.Value
  message : Layout w M
  config : Layout w C
  point : Layout w G
  hashCapacityPred : Nat
  signCapacity : Nat
  hashCountFits : hashCapacityPred + 1 < 2 ^ w
  signCountFits : signCapacity < 2 ^ w
  storageFits : 32 * (cache.key.representation.encoding.words +
    message.representation.encoding.words + config.representation.encoding.words +
    point.representation.encoding.words + cache.value.representation.encoding.words +
    cache.lookup.table.representation.encoding.words +
    (1 + (hashCapacityPred + 1) * (cache.key.representation.encoding.words + point.representation.encoding.words)) +
    (1 + signCapacity * (message.representation.encoding.words + point.representation.encoding.words))) < 2 ^ w

namespace Layouts
variable {w : Nat} {K M R C G : Type} (layout : Layouts w K M R C G)
def hashWords : Nat := 1 + (layout.hashCapacityPred + 1) * (layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words)
def signWords : Nat := 1 + layout.signCapacity * (layout.message.representation.encoding.words + layout.point.representation.encoding.words)
def width : Nat := layout.cache.key.representation.encoding.words +
  layout.message.representation.encoding.words + layout.config.representation.encoding.words +
  layout.point.representation.encoding.words + layout.cache.value.representation.encoding.words +
  layout.cache.lookup.table.representation.encoding.words + layout.hashWords + layout.signWords
theorem fits {words : Nat} (bound : words ≤ 32 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits

def signEntry := layout.message.prod layout.point (layout.fits (by unfold width; omega))
def signLog := layout.signEntry.boundedList layout.signCapacity layout.signCountFits
  (layout.fits (by change layout.signWords ≤ _; unfold width; omega))
def hashEntry := layout.cache.key.prod layout.point (layout.fits (by unfold width; omega))
def recorder : WeightedRecord.Layouts w (K × G) (List (M × G)) where
  entry := layout.hashEntry
  saved := layout.signLog
  capacityPred := layout.hashCapacityPred
  wordFits := layout.cache.wordFits
  countFits := layout.hashCountFits
  storageFits := layout.fits (by
    change 4 * ((layout.cache.key.representation.encoding.words + layout.point.representation.encoding.words) +
      layout.hashWords + layout.signWords) ≤ _
    unfold width; omega)
abbrev hashLog := layout.recorder.log
abbrev logs := layout.recorder.leftOutput
def cacheLogs := layout.cache.lookup.table.prod layout.logs (layout.fits (by
  change _ + (layout.hashWords + layout.signWords) ≤ _; unfold width; omega))
def store : Layout w (Store K M R C G) := layout.config.prod layout.cacheLogs (layout.fits (by
  change _ + (_ + (layout.hashWords + layout.signWords)) ≤ _; unfold width; omega))
def plainInput : Layout w (Request K M R C G) := layout.cache.key.prod layout.store (layout.fits (by
  change _ + (_ + (_ + (layout.hashWords + layout.signWords))) ≤ _; unfold width; omega))
def output := layout.point.prod layout.store (layout.fits (by
  change _ + (_ + (_ + (layout.hashWords + layout.signWords))) ≤ _; unfold width; omega))
abbrev evaluated := CacheRead.output layout.cache
def responseInput := layout.cache.value.prod layout.config (layout.fits (by unfold width; omega))
def savedCache := layout.config.prod layout.cache.lookup.table (layout.fits (by unfold width; omega))
def saved := layout.point.prod layout.savedCache (layout.fits (by
  change _ + (_ + _) ≤ _; unfold width; omega))
def recordPrepared := layout.recorder.leftInput.representation.prod layout.saved.representation (layout.fits (by
  change ((_ + _) + (layout.hashWords + layout.signWords)) + (_ + (_ + _)) ≤ _
  unfold width; omega))
def recorded := layout.logs.representation.prod layout.saved.representation (layout.fits (by
  change (layout.hashWords + layout.signWords) + (_ + (_ + _)) ≤ _; unfold width; omega))

variable [DecidableEq K]
def room (value : Request K M R C G) : Prop :=
  layout.cache.admissible (value.1, layout.default.val, value.2.2.1, ()) ∧
    value.2.2.2.1.length ≤ layout.hashCapacityPred
instance : DecidablePred layout.room := fun _ => inferInstanceAs (Decidable (_ ∧ _))
def input := layout.plainInput.restrict layout.room
def prepared := layout.cache.input.representation.prod layout.input.representation (layout.fits (by
  change (_ + (_ + (_ + 0))) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))) ≤ _
  unfold width; dsimp only [CacheLayout.lookup]; omega))
def post := layout.evaluated.representation.prod layout.input.representation (layout.fits (by
  change (_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))) ≤ _
  unfold width; omega))
def responsePrepared := layout.responseInput.representation.prod layout.post (layout.fits (by
  change (_ + _) + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords))))) ≤ _
  unfold width; omega))
def frame := layout.point.representation.prod layout.post (layout.fits (by
  change _ + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords))))) ≤ _
  unfold width; omega))

end Layouts
end Signatures.Runtime.CaliperBackend.WeightedHash
