import Proofs.Runtime.Caliper.CacheBounds
import Proofs.Runtime.Caliper.BLSResponseNames
import Proofs.Runtime.Caliper.ByteRoute

/-! Fixed-capacity frames for the deterministic part of ROM signing. The
managed table has one reserved insertion slot. LIVE and replay tapes are not
part of this local frame and are retained by the surrounding handler. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROM.Signing
open Caliper BoundedSource

abbrev Table (M F G : Type) := List ((M × G) × F)
abbrev Input (M F G : Type) := (F × F) × G × G × M × Table M F G
abbrev Saved (F G : Type) := (G × F) × (G × G)
abbrev Output (M F G : Type) := (G × F) × (G × G) × Table M F G

structure Layouts (w : Nat) (M F G : Type) where
  message : Layout w M
  scalar : Layout w F
  point : Layout w G
  capacityPred : Nat
  wordFits : 16 < 2 ^ w
  countFits : capacityPred + 1 < 2 ^ w
  storageFits : 64 * (1 + (capacityPred + 1) * (message.representation.encoding.words + point.representation.encoding.words +
    scalar.representation.encoding.words) + 3 * scalar.representation.encoding.words + 3 * point.representation.encoding.words +
    message.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {M F G : Type} (layout : Layouts w M F G)

def width := 1 + (layout.capacityPred + 1) * (layout.message.representation.encoding.words + layout.point.representation.encoding.words +
  layout.scalar.representation.encoding.words) + 3 * layout.scalar.representation.encoding.words +
  3 * layout.point.representation.encoding.words + layout.message.representation.encoding.words
theorem fits_of_le {words : Nat} (bound : words ≤ 64 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def arithmetic : BLSResponse.Layouts w F G where
  scalar := layout.scalar
  point := layout.point
  wordFits := layout.wordFits
  storageFits := layout.fits_of_le (by unfold width; omega)
def key := layout.message.prod layout.point (layout.fits_of_le (by unfold width; omega))
def cache : CacheLayout w (M × G) F where
  key := layout.key
  value := layout.scalar
  capacityPred := layout.capacityPred
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := layout.fits_of_le (by change 8 * (1 + (layout.capacityPred + 1) * (_ + _ + _) + (_ + _) + _) ≤ _; unfold width; omega)
def table := layout.cache.lookup.table
theorem table_words : layout.table.representation.encoding.words =
    1 + (layout.capacityPred + 1) * (layout.message.representation.encoding.words + layout.point.representation.encoding.words +
      layout.scalar.representation.encoding.words) := rfl
def messageTable := layout.message.prod layout.table (layout.fits_of_le (by rw [table_words]; unfold width; omega))
def publicInput := layout.point.prod layout.messageTable (layout.fits_of_le (by
  change _ + (_ + layout.table.representation.encoding.words) ≤ _; rw [table_words]; unfold width; omega))
def base := layout.point.prod layout.publicInput (layout.fits_of_le (by
  change _ + (_ + (_ + layout.table.representation.encoding.words)) ≤ _; rw [table_words]; unfold width; omega))
def rawInput := layout.arithmetic.scalars.prod layout.base (layout.fits_of_le (by
  change (_ + _) + (_ + (_ + (_ + layout.table.representation.encoding.words))) ≤ _; rw [table_words]; unfold width; dsimp only [arithmetic]; omega))
def ready (value : Input M F G) : Prop := value.2.2.2.2.length ≤ layout.capacityPred
instance (value : Input M F G) : Decidable (layout.ready value) := inferInstanceAs (Decidable (_ ≤ _))
def input := layout.rawInput.restrict layout.ready
theorem input_words : layout.input.representation.encoding.words = 2 * layout.scalar.representation.encoding.words +
    2 * layout.point.representation.encoding.words + layout.message.representation.encoding.words + layout.table.representation.encoding.words := by
  change (_ + _) + (_ + (_ + (_ + _))) = _; dsimp only [arithmetic]; omega
theorem input_le : layout.input.representation.encoding.words ≤ layout.width := by
  rw [input_words, table_words]; unfold width; omega

def duplicated : Representation w (layout.input.Value × layout.input.Value) := layout.input.representation.prod layout.input.representation
  (layout.fits_of_le (by have := layout.input_le; omega))
def frame : Representation w (layout.point.Value × layout.input.Value) := layout.point.representation.prod layout.input.representation
  (layout.fits_of_le (by have := layout.input_le; unfold width at *; omega))
def reply := layout.point.prod layout.scalar (layout.fits_of_le (by unfold width; omega))
def saved : Layout w (Saved F G) := layout.reply.prod layout.arithmetic.points (layout.fits_of_le (by
  change (_ + _) + (_ + _) ≤ _; unfold width; dsimp only [arithmetic]; omega))
def store := layout.arithmetic.points.prod layout.table (layout.fits_of_le (by
  change (_ + _) + _ ≤ _; rw [table_words]; unfold width; dsimp only [arithmetic]; omega))
def output : Layout w (Output M F G) := layout.reply.prod layout.store (layout.fits_of_le (by
  change (_ + _) + ((_ + _) + _) ≤ _; rw [table_words]; unfold width; dsimp only [arithmetic]; omega))
theorem output_le : layout.output.representation.encoding.words ≤ layout.width := by
  change (_ + _) + ((_ + _) + layout.table.representation.encoding.words) ≤ _
  rw [table_words]; unfold width; dsimp only [arithmetic]; omega

variable [DecidableEq M] [DecidableEq G]
def work := layout.cache.input.prod layout.saved (layout.fits_of_le (by
  change layout.cache.lookup.input.representation.encoding.words + ((_ + _) + (_ + _)) ≤ _
  rw [LookupLayout.input_words]
  change (1 + (layout.capacityPred + 1) * (_ + _ + _) + (_ + _) + _) + ((_ + _) + (_ + _)) ≤ _
  unfold width; dsimp only [arithmetic, cache, CacheLayout.lookup]; omega))
theorem work_le : layout.work.representation.encoding.words ≤ 2 * layout.width := by
  change layout.cache.lookup.input.representation.encoding.words + ((_ + _) + (_ + _)) ≤ _
  rw [LookupLayout.input_words]
  change (1 + (layout.capacityPred + 1) * (_ + _ + _) + (_ + _) + _) + ((_ + _) + (_ + _)) ≤ _
  unfold width; dsimp only [arithmetic, cache, CacheLayout.lookup]; omega
def programmed : Representation w (layout.table.Value × layout.saved.Value) := layout.table.representation.prod layout.saved.representation
  (layout.fits_of_le (by change _ + ((_ + _) + (_ + _)) ≤ _; rw [table_words]; unfold width; dsimp only [arithmetic]; omega))

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrROM.Signing
