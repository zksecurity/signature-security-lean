import Proofs.Runtime.Caliper.CacheReadBuffers

/-! A private cache request with an explicitly retained coefficient and
accumulator. The cache request carries its hit-or-room invariant. Saved values
are represented storage, and the executed retain wrapper copies them. -/

namespace Signatures.Runtime.CaliperBackend.CacheAccumulate
open Caliper BoundedSource

structure Layouts (w : Nat) (K F R : Type) where
  cache : CacheLayout w K R
  coefficient : Layout w F
  storageFits : 16 * (cache.lookup.width + coefficient.representation.encoding.words + cache.value.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {K F R : Type} (layout : Layouts w K F R)
def width : Nat := layout.cache.lookup.width + layout.coefficient.representation.encoding.words + layout.cache.value.representation.encoding.words
theorem fits_of_le {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits
theorem cache_width : layout.cache.lookup.width = layout.cache.key.representation.encoding.words +
    layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words := by
  rw [LookupLayout.table_words]
  dsimp only [LookupLayout.width]
  change 1 + _ + layout.cache.key.representation.encoding.words +
    layout.cache.value.representation.encoding.words =
      layout.cache.key.representation.encoding.words + layout.cache.value.representation.encoding.words + (1 + _)
  omega
theorem base_sizes : layout.cache.value.representation.encoding.words ≤ layout.width ∧
    layout.coefficient.representation.encoding.words ≤ layout.width ∧
    layout.cache.lookup.table.representation.encoding.words ≤ layout.width ∧
    layout.cache.lookup.width ≤ layout.width ∧
    2 * layout.cache.value.representation.encoding.words ≤ layout.width := by
  dsimp only [width]
  rw [cache_width]
  omega
def saved : Layout w (F × R) := layout.coefficient.prod layout.cache.value
  (layout.fits_of_le (by have := layout.base_sizes; omega))
def pair : Layout w (R × R) := layout.cache.value.prod layout.cache.value
  (layout.fits_of_le (by have := layout.base_sizes; omega))
def combine : Layout w (F × (R × R)) := layout.coefficient.prod layout.pair
  (layout.fits_of_le (by change _ + (_ + _) ≤ _; have := layout.base_sizes; omega))
def returned : Layout w ((R × List (K × R)) × (F × R)) := (CacheRead.output layout.cache).prod layout.saved
  (layout.fits_of_le (by
    change (_ + _) + (_ + _) ≤ _
    have := layout.base_sizes
    omega))
@[simp] theorem saved_words : layout.saved.representation.encoding.words =
    layout.coefficient.representation.encoding.words + layout.cache.value.representation.encoding.words := rfl
@[simp] theorem pair_words : layout.pair.representation.encoding.words = 2 * layout.cache.value.representation.encoding.words := by
  change _ + _ = _; omega
@[simp] theorem combine_words : layout.combine.representation.encoding.words =
    layout.coefficient.representation.encoding.words + 2 * layout.cache.value.representation.encoding.words := by
  change _ + (_ + _) = _; omega
@[simp] theorem returned_words : layout.returned.representation.encoding.words =
    layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words +
      layout.coefficient.representation.encoding.words + layout.cache.value.representation.encoding.words := by
  change (_ + _) + (_ + _) = _; omega
theorem sizes : layout.saved.representation.encoding.words ≤ layout.width ∧
    layout.pair.representation.encoding.words ≤ layout.width ∧
    layout.combine.representation.encoding.words ≤ layout.width ∧
    layout.returned.representation.encoding.words ≤ layout.width ∧
    (CacheRead.output layout.cache).representation.encoding.words ≤ layout.width := by
  simp only [saved_words, pair_words, combine_words, returned_words]
  change _ ∧ _ ∧ _ ∧ _ ∧ layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words ≤ _
  dsimp only [width]
  rw [cache_width]
  omega

variable [DecidableEq K]
def input : Layout w (CacheLayout.Input K R × (F × R)) := layout.cache.input.prod layout.saved
  (layout.fits_of_le (by
    have := layout.sizes
    have := layout.base_sizes
    change layout.cache.lookup.input.representation.encoding.words + _ ≤ _
    rw [LookupLayout.input_words]
    omega))
@[simp] theorem input_words : layout.input.representation.encoding.words = layout.width := by
  change layout.cache.lookup.input.representation.encoding.words + layout.saved.representation.encoding.words = _
  rw [LookupLayout.input_words, saved_words]
  dsimp only [width]
  omega

end Layouts

variable {w : Nat} {K F R : Type} (layout : Layouts w K F R)
include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (fits : buffers < 2 ^ w) : body.program.savedBuffer < 2 ^ w := by
  have := layout.cache.wordFits
  dsimp only [Realizer.savedBuffer]
  omega

end Signatures.Runtime.CaliperBackend.CacheAccumulate
