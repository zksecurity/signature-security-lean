import Proofs.Runtime.Caliper.CacheReadBounds
import Proofs.Runtime.Caliper.SumContextBounds

/-! A cache read whose fresh-entry sampler carries represented mutable state.
The state is ordinary runtime data. The cache frame and fresh state have
explicit combined address bounds; no closure captures an uncharged input. -/
namespace Signatures.Runtime.CaliperBackend.StatefulCacheRead
open Caliper BoundedSource

structure Layouts (w : Nat) (K V S : Type) where
  cache : CacheLayout w K V
  saved : Representation w S
  storageFits : 8 * (cache.lookup.width + saved.encoding.words + cache.value.representation.encoding.words + 1) < 2 ^ w

namespace Layouts
variable {w : Nat} {K V S : Type} (layout : Layouts w K V S)

def width : Nat := layout.cache.lookup.width + layout.saved.encoding.words + layout.cache.value.representation.encoding.words + 1
theorem fits_of_le {words : Nat} (bound : words ≤ 8 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

theorem sizes : layout.cache.lookup.input.representation.encoding.words ≤ layout.width ∧
    (CacheRead.output layout.cache).representation.encoding.words ≤ layout.width ∧
    (CacheRead.yes layout.cache).representation.encoding.words ≤ layout.width ∧
    (CacheRead.no layout.cache).representation.encoding.words ≤ layout.width ∧
    layout.saved.encoding.words ≤ layout.width ∧
    layout.cache.value.representation.encoding.words ≤ layout.width := by
  simp only [LookupLayout.input_words, CacheRead.yes_words, CacheRead.no_words, CacheLayout.frame_words]
  change layout.cache.lookup.width ≤ _ ∧
    layout.cache.value.representation.encoding.words + layout.cache.lookup.table.representation.encoding.words ≤ _ ∧ _
  rw [LookupLayout.table_words]
  dsimp only [width, LookupLayout.width, CacheLayout.lookup]
  omega

def freshOutput : Representation w (layout.cache.value.Value × S) :=
  layout.cache.value.representation.prod layout.saved (layout.fits_of_le (by have := layout.sizes; omega))
def input [DecidableEq K] : Representation w (layout.cache.input.Value × S) :=
  layout.cache.input.representation.prod layout.saved (layout.fits_of_le (by
    change layout.cache.lookup.input.representation.encoding.words + _ ≤ _
    have := layout.sizes; omega))
def output : Representation w ((CacheRead.output layout.cache).Value × S) :=
  (CacheRead.output layout.cache).representation.prod layout.saved (layout.fits_of_le (by have := layout.sizes; omega))
def hitInput : Representation w ((CacheRead.yes layout.cache).Value × S) :=
  (CacheRead.yes layout.cache).representation.prod layout.saved (layout.fits_of_le (by have := layout.sizes; omega))
def missInput : Representation w ((CacheRead.no layout.cache).Value × S) :=
  (CacheRead.no layout.cache).representation.prod layout.saved (layout.fits_of_le (by have := layout.sizes; omega))
def choice : Representation w (((CacheRead.yes layout.cache).Value × S) ⊕ ((CacheRead.no layout.cache).Value × S)) :=
  layout.hitInput.sum layout.missInput (width_pos layout.cache.wordFits) (layout.fits_of_le (by
    change 1 + max ((_ : Nat) + _) (_ + _) ≤ _
    have positive : 0 < layout.width := by dsimp only [width]; omega
    have := layout.sizes
    simp only [CacheRead.yes_words, CacheRead.no_words] at *
    omega))

def sampled : Representation w ((layout.cache.value.Value × S) × (CacheRead.no layout.cache).Value) :=
  layout.freshOutput.prod (CacheRead.no layout.cache).representation (layout.fits_of_le (by
    change (_ + _) + _ ≤ _; have := layout.sizes; omega))
def insertedInput : Representation w ((CacheRead.drawn layout.cache).Value × S) :=
  (CacheRead.drawn layout.cache).representation.prod layout.saved (layout.fits_of_le (by
    change (_ + _) + _ ≤ _; have := layout.sizes; omega))

end Layouts
end Signatures.Runtime.CaliperBackend.StatefulCacheRead
