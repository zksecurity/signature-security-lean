import Proofs.Runtime.Caliper.CacheFinishBounds

/-! Fixed-capacity layouts across the cache's primitive draw. The saved miss
frame retains the observed false result and its free-slot witness. -/

namespace Signatures.Runtime.CaliperBackend.CacheRead

open Caliper BoundedSource

variable {w : Nat} {K V : Type} (layout : CacheLayout w K V)

def yes : Layout w (CacheLayout.Frame K V) := GuardedBranch.yesInput layout.frame (fun value => value.1.1)
def no : Layout w (CacheLayout.Frame K V) := GuardedBranch.noInput layout.frame (fun value => value.1.1)

@[simp] theorem yes_words : (yes layout).representation.encoding.words = layout.frame.representation.encoding.words := rfl
@[simp] theorem no_words : (no layout).representation.encoding.words = layout.frame.representation.encoding.words := rfl

theorem outputFits : layout.value.representation.encoding.words + layout.lookup.table.representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by simp [LookupLayout.width]; dsimp [CacheLayout.lookup]; omega)

def output : Layout w (V × List (K × V)) := layout.value.prod layout.lookup.table (outputFits layout)

theorem drawnFits : layout.value.representation.encoding.words + (no layout).representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by simp; dsimp [CacheLayout.lookup, LookupLayout.width]; omega)

def drawn : Layout w (V × CacheLayout.Frame K V) := layout.value.prod (no layout) (drawnFits layout)

@[simp] theorem drawn_words : (drawn layout).representation.encoding.words =
    layout.value.representation.encoding.words + layout.frame.representation.encoding.words := rfl

theorem drawn_duplicateFits : (drawn layout).representation.encoding.words + (drawn layout).representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by simp; dsimp [CacheLayout.lookup, LookupLayout.width]; omega)

theorem drawn_keyFits : layout.key.representation.encoding.words + (drawn layout).representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by simp; dsimp [CacheLayout.lookup, LookupLayout.width]; omega)

theorem drawn_entryFits : layout.lookup.entry.representation.encoding.words + (drawn layout).representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by simp; dsimp [CacheLayout.lookup, LookupLayout.width]; omega)

theorem drawn_valueFits : layout.value.representation.encoding.words + (drawn layout).representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by simp; dsimp [CacheLayout.lookup, LookupLayout.width]; omega)

theorem frame_valueFits : layout.value.representation.encoding.words + layout.lookup.accumulatorTail.representation.encoding.words < 2 ^ w :=
  layout.lookup.fits_of_le (by simp; dsimp [CacheLayout.lookup, LookupLayout.width]; omega)

theorem frame_duplicateFits : layout.lookup.accumulatorTail.representation.encoding.words + layout.lookup.accumulatorTail.representation.encoding.words < 2 ^ w :=
  layout.frame_duplicateFits

end Signatures.Runtime.CaliperBackend.CacheRead
