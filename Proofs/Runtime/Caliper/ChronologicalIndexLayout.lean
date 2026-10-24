import Proofs.Runtime.Caliper.ConstructedLiteral
import Proofs.Runtime.Caliper.ConstructedStorage
import Proofs.Runtime.Caliper.EncodedEquality
import Proofs.Runtime.Caliper.FoldNames

/-! A chronological key index in a newest-first association list. The domain
of keys is arbitrary; only the stored list and encoded values are bounded.
Iteration-dependent counters prove every increment fits in one word. -/
namespace Signatures.Runtime.CaliperBackend.ChronologicalIndex
open Caliper BoundedSource

structure Layouts (w : Nat) (K V : Type) where
  key : Layout w K
  value : Layout w V
  capacity : Nat
  wordFits : 16 < 2 ^ w
  countFits : capacity + 1 ≤ 2 ^ w
  storageFits : 16 * (4 + (capacity + 2) * (key.representation.encoding.words + value.representation.encoding.words) +
    key.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {K V : Type} (layout : Layouts w K V)
def width := 4 + (layout.capacity + 2) * (layout.key.representation.encoding.words + layout.value.representation.encoding.words) +
  layout.key.representation.encoding.words
theorem fits {n : Nat} (bound : n ≤ 16 * layout.width) : n < 2 ^ w := bound.trans_lt layout.storageFits
def boolean := DataImplementation.boolLayout w (width_pos layout.wordFits)
def counter (i : Fin (layout.capacity + 1)) := Layout.counter w (i.val + 1) (width_pos layout.wordFits)
  (by have := layout.countFits; omega)
def state (i : Fin (layout.capacity + 1)) := layout.boolean.prod (layout.counter i)
  (by change 1 + 1 < _; have := layout.wordFits; omega)
def result := layout.state ⟨layout.capacity, by omega⟩
def entry := layout.key.prod layout.value (layout.fits (by unfold width; nlinarith))
def list := layout.entry.boundedList layout.capacity (by have := layout.countFits; omega)
  (layout.fits (by
    change 1 + layout.capacity * (layout.key.representation.encoding.words + layout.value.representation.encoding.words) ≤ _
    unfold width
    nlinarith))
def input := layout.key.prod layout.list (layout.fits (by
  change _ + (1 + layout.capacity * (layout.key.representation.encoding.words + layout.value.representation.encoding.words)) ≤ _
  unfold width; nlinarith))
def stateTail (i : Fin (layout.capacity + 1)) := (layout.state i).prod layout.key
  (layout.fits (by change (1 + 1) + _ ≤ _; unfold width; nlinarith))
theorem argFits (i : Fin layout.capacity) : layout.entry.representation.encoding.words +
    (layout.state i.castSucc).representation.encoding.words + layout.key.representation.encoding.words < 2 ^ w :=
  layout.fits (by change (_ + _) + (1 + 1) + _ ≤ _; unfold width; nlinarith)
theorem frameFits (i : Fin (layout.capacity + 1)) : 1 + (layout.capacity - i.val) * layout.entry.representation.encoding.words +
    (layout.state i).representation.encoding.words + 2 * layout.key.representation.encoding.words < 2 ^ w := by
  apply layout.fits
  have counts := Nat.mul_le_mul_right (layout.key.representation.encoding.words + layout.value.representation.encoding.words)
    (Nat.sub_le layout.capacity i.val)
  change 1 + (layout.capacity - i.val) * (_ + _) + (1 + 1) + 2 * _ ≤ _
  unfold width
  nlinarith
def body (i : Fin layout.capacity) := FoldImplementation.bodyInput layout.entry (layout.state i.castSucc) layout.key (layout.argFits i)
def frame := FoldImplementation.input layout.entry (layout.state 0) layout.key layout.capacity
  (by have := layout.countFits; omega) (layout.frameFits 0)
theorem sizes (i : Fin (layout.capacity + 1)) :
    layout.key.representation.encoding.words ≤ layout.width ∧ layout.entry.representation.encoding.words ≤ layout.width ∧
    layout.list.representation.encoding.words ≤ layout.width ∧ layout.input.representation.encoding.words ≤ layout.width ∧
    (layout.state i).representation.encoding.words = 2 ∧ (layout.stateTail i).representation.encoding.words ≤ layout.width := by
  change _ ≤ _ ∧ (_ + _) ≤ _ ∧ (1 + layout.capacity * (_ + _)) ≤ _ ∧
    _ + (1 + layout.capacity * (_ + _)) ≤ _ ∧ 1 + 1 = 2 ∧ (1 + 1) + _ ≤ _
  unfold width
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, rfl, by nlinarith⟩
theorem body_size (i : Fin layout.capacity) : (layout.body i).representation.encoding.words ≤ 2 * layout.width := by
  change layout.entry.representation.encoding.words + (layout.stateTail i.castSucc).representation.encoding.words ≤ _
  have := layout.sizes i.castSucc
  omega
theorem duplicate (i : Fin layout.capacity) : (layout.body i).representation.encoding.words + (layout.body i).representation.encoding.words < 2 ^ w :=
  layout.fits (by have := layout.body_size i; omega)
theorem tagged (i : Fin layout.capacity) : 1 + (layout.body i).representation.encoding.words < 2 ^ w :=
  layout.fits (by have := layout.body_size i; unfold width at *; omega)
end Layouts

def step {K V : Type} [DecidableEq K] (value : (K × V) × ((Bool × Nat) × K)) : Bool × Nat :=
  if value.1.1 = value.2.2 then (true, 0) else (value.2.1.1, value.2.1.2 + 1)
def value {K V : Type} [DecidableEq K] (input : K × List (K × V)) : Bool × Nat :=
  (input.2.reverse.any (fun entry => decide (entry.1 = input.1)), input.2.reverse.findIdx (fun entry => decide (entry.1 = input.1)))
theorem fold_value {K V : Type} [DecidableEq K] (key : K) (entries : List (K × V)) :
    FoldImplementation.sourceFold step (entries, (false, 0), key) = value (key, entries) := by
  induction entries using List.reverseRecOn with
  | nil => rfl
  | append_singleton entries entry ih =>
    change entries.foldl (fun state entry => step (entry, state, key)) (false, 0) = _ at ih
    simp only [FoldImplementation.sourceFold, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih]
    by_cases equal : entry.1 = key <;>
      simp [step, value, List.reverse_append, List.findIdx_cons, equal]

end Signatures.Runtime.CaliperBackend.ChronologicalIndex
