import Proofs.Runtime.Caliper.LookupLayout
import Proofs.Runtime.Caliper.RestrictedLayout
import Proofs.Runtime.Lookup

/-! A nonempty fixed-capacity cache layout. `capacityPred + 1` is the maximum
number of stored entries. Full tables remain admitted for hits; a miss needs
one free slot. Scheme-level reachability must establish that input invariant. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

structure CacheLayout (w : Nat) (K V : Type) where
  key : Layout w K
  value : Layout w V
  capacityPred : Nat
  wordFits : 16 < 2 ^ w
  countFits : capacityPred + 1 < 2 ^ w
  storageFits : 8 * (1 + (capacityPred + 1) * (key.representation.encoding.words + value.representation.encoding.words) +
    key.representation.encoding.words + value.representation.encoding.words) < 2 ^ w

namespace CacheLayout

variable {w : Nat} {K V : Type} (layout : CacheLayout w K V)

def lookup : LookupLayout w K V :=
  ⟨layout.key, layout.value, layout.capacityPred + 1, layout.wordFits, layout.countFits, layout.storageFits⟩

abbrev Input (K V : Type) := K × (V × (List (K × V) × Unit))
abbrev Frame (K V : Type) := (Bool × V) × Input K V

def frameGuard (value : Frame K V) : Prop :=
  value.1.1 = false → value.2.2.2.1.length ≤ layout.capacityPred

instance (value : Frame K V) : Decidable (layout.frameGuard value) := inferInstanceAs (Decidable (_ → _))

def frame : Layout w (Frame K V) := layout.lookup.accumulatorTail.restrict layout.frameGuard

@[simp] theorem frame_words : layout.frame.representation.encoding.words =
    1 + layout.value.representation.encoding.words + layout.lookup.width := by
  simpa only [frame, Layout.restrict_words, lookup] using layout.lookup.accumulatorTail_words

theorem entryTableFits : layout.lookup.entry.representation.encoding.words + layout.lookup.table.representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by simp [LookupLayout.width]; omega)

def entryTable : Layout w ((K × V) × List (K × V)) :=
  layout.lookup.entry.prod layout.lookup.table layout.entryTableFits

theorem fixedConsFits : 1 + (layout.capacityPred + 2) * layout.lookup.entry.representation.encoding.words < 2 ^ w := by
  apply layout.lookup.fits_of_le
  simp only [LookupLayout.entry_words]
  change 1 + (layout.capacityPred + 2) * (layout.key.representation.encoding.words + layout.value.representation.encoding.words) ≤
    8 * (1 + (layout.capacityPred + 1) * (layout.key.representation.encoding.words + layout.value.representation.encoding.words) +
      layout.key.representation.encoding.words + layout.value.representation.encoding.words)
  nlinarith

theorem frame_duplicateFits : layout.frame.representation.encoding.words + layout.frame.representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by rw [frame_words]; dsimp [LookupLayout.width, lookup]; omega)

theorem frame_tagFits : 1 + layout.frame.representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by rw [frame_words]; dsimp [LookupLayout.width, lookup]; omega)

variable [DecidableEq K]

def admissible (value : Input K V) : Prop :=
  (lookupValue value.1 value.2.1 value.2.2.1).1 = false → value.2.2.1.length ≤ layout.capacityPred

instance (value : Input K V) : Decidable (layout.admissible value) := inferInstanceAs (Decidable (_ → _))

def input : Layout w (Input K V) := layout.lookup.input.restrict layout.admissible

end CacheLayout
end Signatures.Runtime.CaliperBackend.BoundedSource
