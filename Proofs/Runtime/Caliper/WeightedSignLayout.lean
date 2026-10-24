import Proofs.Runtime.Caliper.GeneratedWeightedOracle
import Proofs.Runtime.Caliper.WeightedRecord
import Proofs.Runtime.Caliper.ByteRoute

/-! Frames for weighted signing. Cache indices and signed messages have
independent types, and their reply logs have independent capacities. -/
namespace Signatures.Runtime.CaliperBackend.WeightedSign
open Caliper BoundedSource

abbrev Logs (K M G : Type) := Model.LazyAGM.Transcript K M G
abbrev Store (K M R C G : Type) := C × (List (K × R) × Logs K M G)
abbrev Request (K M R C G : Type) := M × Store K M R C G

structure Layouts (w : Nat) (K M F R C G : Type) where
  evaluation : CacheAccumulate.Layouts w K F R
  message : Layout w M
  config : Layout w C
  point : Layout w G
  hashCapacity : Nat
  signCapacityPred : Nat
  hashCountFits : hashCapacity < 2 ^ w
  signCountFits : signCapacityPred + 1 < 2 ^ w
  storageFits : 32 * (evaluation.cache.key.representation.encoding.words +
    message.representation.encoding.words + config.representation.encoding.words +
    point.representation.encoding.words + evaluation.cache.value.representation.encoding.words +
    evaluation.cache.lookup.table.representation.encoding.words +
    (1 + hashCapacity * (evaluation.cache.key.representation.encoding.words + point.representation.encoding.words)) +
    (1 + (signCapacityPred + 1) * (message.representation.encoding.words + point.representation.encoding.words))) < 2 ^ w

namespace Layouts
variable {w : Nat} {K M F R C G : Type} (layout : Layouts w K M F R C G)
def hashWords : Nat := 1 + layout.hashCapacity * (layout.evaluation.cache.key.representation.encoding.words + layout.point.representation.encoding.words)
def signWords : Nat := 1 + (layout.signCapacityPred + 1) * (layout.message.representation.encoding.words + layout.point.representation.encoding.words)
def width : Nat := layout.evaluation.cache.key.representation.encoding.words +
  layout.message.representation.encoding.words + layout.config.representation.encoding.words +
  layout.point.representation.encoding.words + layout.evaluation.cache.value.representation.encoding.words +
  layout.evaluation.cache.lookup.table.representation.encoding.words + layout.hashWords + layout.signWords
theorem fits {words : Nat} (bound : words ≤ 32 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits

def hashEntry := layout.evaluation.cache.key.prod layout.point (layout.fits (by unfold width; omega))
def hashLog := layout.hashEntry.boundedList layout.hashCapacity layout.hashCountFits
  (layout.fits (by change layout.hashWords ≤ _; unfold width; omega))
def signEntry := layout.message.prod layout.point (layout.fits (by unfold width; omega))
def recorder : WeightedRecord.Layouts w (M × G) (List (K × G)) where
  entry := layout.signEntry
  saved := layout.hashLog
  capacityPred := layout.signCapacityPred
  wordFits := layout.evaluation.cache.wordFits
  countFits := layout.signCountFits
  storageFits := layout.fits (by
    change 4 * ((layout.message.representation.encoding.words + layout.point.representation.encoding.words) +
      layout.signWords + layout.hashWords) ≤ _
    unfold width; omega)
abbrev signLog := layout.recorder.log
abbrev logs := layout.recorder.rightOutput
def cacheLogs := layout.evaluation.cache.lookup.table.prod layout.logs (layout.fits (by
  change _ + (layout.hashWords + layout.signWords) ≤ _; unfold width; omega))
def store : Layout w (Store K M R C G) := layout.config.prod layout.cacheLogs (layout.fits (by
  change _ + (_ + (layout.hashWords + layout.signWords)) ≤ _; unfold width; omega))
def plainInput : Layout w (Request K M R C G) := layout.message.prod layout.store (layout.fits (by
  change _ + (_ + (_ + (layout.hashWords + layout.signWords))) ≤ _; unfold width; omega))
def room (value : Request K M R C G) : Prop := value.2.2.2.2.length ≤ layout.signCapacityPred
instance : DecidablePred layout.room := fun _ => inferInstanceAs (Decidable (_ ≤ _))
def input := layout.plainInput.restrict layout.room
def output := layout.point.prod layout.store (layout.fits (by
  change _ + (_ + (_ + (layout.hashWords + layout.signWords))) ≤ _; unfold width; omega))
abbrev evaluated := (WeightedRows.rows layout.evaluation).state
def evaluationInput := layout.message.representation.prod layout.evaluated.representation
  (layout.fits (by change _ + (_ + _) ≤ _; dsimp only [WeightedRows.rows]; unfold width; omega))
def prepared := layout.evaluationInput.prod layout.input.representation (layout.fits (by
  change (_ + (_ + _)) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))) ≤ _
  dsimp only [WeightedRows.rows]; unfold width; omega))
def post := layout.evaluated.representation.prod layout.input.representation (layout.fits (by
  change (_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords)))) ≤ _
  dsimp only [WeightedRows.rows]; unfold width; omega))
def responseInput := layout.evaluation.cache.value.prod layout.config (layout.fits (by unfold width; omega))
def responsePrepared := layout.responseInput.representation.prod layout.post (layout.fits (by
  change (_ + _) + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords))))) ≤ _
  dsimp only [WeightedRows.rows]; unfold width; omega))
def frame := layout.point.representation.prod layout.post (layout.fits (by
  change _ + ((_ + _) + (_ + (_ + (_ + (layout.hashWords + layout.signWords))))) ≤ _
  dsimp only [WeightedRows.rows]; unfold width; omega))
def savedCache := layout.config.prod layout.evaluation.cache.lookup.table (layout.fits (by unfold width; omega))
def saved := layout.point.prod layout.savedCache (layout.fits (by
  change _ + (_ + _) ≤ _; unfold width; omega))
def recordPrepared := layout.recorder.rightInput.representation.prod layout.saved.representation (layout.fits (by
  change ((_ + _) + (layout.hashWords + layout.signWords)) + (_ + (_ + _)) ≤ _
  unfold width; omega))
def recorded := layout.logs.representation.prod layout.saved.representation (layout.fits (by
  change (layout.hashWords + layout.signWords) + (_ + (_ + _)) ≤ _
  unfold width; omega))

end Layouts
end Signatures.Runtime.CaliperBackend.WeightedSign
