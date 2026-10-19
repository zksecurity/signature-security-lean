import Signatures.Runtime.Caliper.ListIndexBounds
import Signatures.Runtime.Caliper.ListReverseBounds
import Signatures.Runtime.AttachTable

/-! Representations for positional attachment to a stored key list. Key and
coefficient capacities are independent. Stage domains bound both the growing
row list and its counter; no key-domain enumeration is represented. -/

namespace Signatures.Runtime.CaliperBackend.AttachRows
open Caliper BoundedSource

structure Layouts (w : Nat) (K V : Type) where
  key : Layout w K
  value : Layout w V
  capacity : Nat
  coefficients : Nat
  wordFits : 16 < 2 ^ w
  counterFits : capacity + 2 ≤ 2 ^ w
  coefficientCountFits : coefficients < 2 ^ w
  storageFits : 16 * (4 + (capacity + 1) *
    (key.representation.encoding.words + value.representation.encoding.words) +
    (coefficients + 1) * value.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {K V : Type} (layout : Layouts w K V)

def width : Nat := 4 + (layout.capacity + 1) *
  (layout.key.representation.encoding.words + layout.value.representation.encoding.words) +
  (layout.coefficients + 1) * layout.value.representation.encoding.words
theorem fits_of_le {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits
theorem countFits : layout.capacity < 2 ^ w := by have := layout.counterFits; omega
def row : Layout w (K × V) := layout.key.prod layout.value (layout.fits_of_le (by dsimp only [width]; nlinarith))
def keys : Layout w (List K) := layout.key.boundedList layout.capacity layout.countFits
  (layout.fits_of_le (by dsimp only [width]; nlinarith))
def values : Layout w (List V) := layout.value.boundedList layout.coefficients layout.coefficientCountFits
  (layout.fits_of_le (by dsimp only [width]; nlinarith))
def env : Layout w (V × List V) := layout.value.prod layout.values
  (layout.fits_of_le (by change _ + (1 + layout.coefficients * _) ≤ _; dsimp only [width]; nlinarith))
def input : Layout w (List K × (V × List V)) := layout.keys.prod layout.env
  (layout.fits_of_le (by change (1 + layout.capacity * _) + (_ + (1 + layout.coefficients * _)) ≤ _; dsimp only [width]; nlinarith))
def counter (i : Fin (layout.capacity + 1)) : Layout w Nat :=
  Layout.counter w (i.val + 1) (width_pos layout.wordFits) (by have := layout.counterFits; omega)
def rows (i : Fin (layout.capacity + 1)) : Layout w (List (K × V)) :=
  layout.row.boundedList i.val (by have := layout.countFits; omega)
    (layout.fits_of_le (by
      have := Nat.mul_le_mul_right (layout.key.representation.encoding.words + layout.value.representation.encoding.words)
        (show i.val ≤ layout.capacity + 1 by omega)
      change 1 + i.val * (_ + _) ≤ _
      dsimp only [width]; omega))
def states (i : Fin (layout.capacity + 1)) : Layout w (Nat × List (K × V)) :=
  (layout.counter i).prod (layout.rows i) (layout.fits_of_le (by
    have := Nat.mul_le_mul_right (layout.key.representation.encoding.words + layout.value.representation.encoding.words)
      (show i.val ≤ layout.capacity + 1 by omega)
    change 1 + (1 + i.val * (_ + _)) ≤ _
    dsimp only [width]; omega))

@[simp] theorem row_words : layout.row.representation.encoding.words =
    layout.key.representation.encoding.words + layout.value.representation.encoding.words := rfl
@[simp] theorem keys_words : layout.keys.representation.encoding.words = 1 + layout.capacity * layout.key.representation.encoding.words := rfl
@[simp] theorem values_words : layout.values.representation.encoding.words = 1 + layout.coefficients * layout.value.representation.encoding.words := rfl
@[simp] theorem env_words : layout.env.representation.encoding.words = 1 + (layout.coefficients + 1) * layout.value.representation.encoding.words := by
  change _ + (1 + layout.coefficients * _) = _; ring
@[simp] theorem counter_words (i : Fin (layout.capacity + 1)) : (layout.counter i).representation.encoding.words = 1 := rfl
@[simp] theorem rows_words (i : Fin (layout.capacity + 1)) : (layout.rows i).representation.encoding.words = 1 + i.val * layout.row.representation.encoding.words := rfl
@[simp] theorem states_words (i : Fin (layout.capacity + 1)) : (layout.states i).representation.encoding.words = 2 + i.val * layout.row.representation.encoding.words := by
  change 1 + (1 + i.val * _) = _; omega

theorem base_sizes : layout.key.representation.encoding.words ≤ layout.width ∧
    layout.value.representation.encoding.words ≤ layout.width ∧
    layout.row.representation.encoding.words ≤ layout.width ∧
    layout.keys.representation.encoding.words ≤ layout.width ∧
    layout.values.representation.encoding.words ≤ layout.width ∧
    layout.env.representation.encoding.words ≤ layout.width ∧
    layout.input.representation.encoding.words ≤ layout.width := by
  simp only [input, Layout.prod_words, row_words, keys_words, values_words, env_words]
  dsimp only [width]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith
theorem stage_sizes (i : Fin (layout.capacity + 1)) :
    (layout.rows i).representation.encoding.words ≤ layout.width ∧
    (layout.states i).representation.encoding.words ≤ layout.width := by
  have := Nat.mul_le_mul_right layout.row.representation.encoding.words (show i.val ≤ layout.capacity + 1 by omega)
  simp only [row_words] at this
  simp only [rows_words, states_words, row_words]
  dsimp only [width]
  constructor <;> omega
theorem argFits (i : Fin layout.capacity) : layout.key.representation.encoding.words +
    (layout.states i.castSucc).representation.encoding.words + layout.env.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.base_sizes; have := layout.stage_sizes i.castSucc; omega)
theorem frameFits (i : Fin (layout.capacity + 1)) :
    1 + (layout.capacity - i.val) * layout.key.representation.encoding.words +
      (layout.states i).representation.encoding.words + 2 * layout.env.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by
    have h := Nat.mul_le_mul_right layout.key.representation.encoding.words (Nat.sub_le layout.capacity i.val)
    have := layout.base_sizes; have := layout.stage_sizes i
    have := layout.keys_words
    omega)
def body (i : Fin layout.capacity) := FoldImplementation.bodyInput layout.key (layout.states i.castSucc) layout.env (layout.argFits i)
def frame := FoldImplementation.input layout.key (layout.states 0) layout.env layout.capacity layout.countFits (layout.frameFits 0)
def context (i : Fin layout.capacity) := (layout.states i.castSucc).prod layout.env (by have := layout.argFits i; omega)
theorem body_size (i : Fin layout.capacity) : (layout.body i).representation.encoding.words ≤ 3 * layout.width := by
  change layout.key.representation.encoding.words + ((layout.states i.castSucc).representation.encoding.words + layout.env.representation.encoding.words) ≤ _
  have := layout.base_sizes; have := layout.stage_sizes i.castSucc; omega
theorem context_size (i : Fin layout.capacity) : (layout.context i).representation.encoding.words ≤ 2 * layout.width := by
  change (layout.states i.castSucc).representation.encoding.words + layout.env.representation.encoding.words ≤ _
  have := layout.base_sizes; have := layout.stage_sizes i.castSucc; omega

def indexing (i : Fin layout.capacity) : ListIndex.Layouts w V where
  value := layout.value
  capacity := layout.coefficients
  indexBound := i.val + 1
  indexPositive := by omega
  indexFits := by have := layout.counterFits; omega
  wordFits := layout.wordFits
  countFits := layout.coefficientCountFits
  storageFits := layout.fits_of_le (by dsimp only [width]; nlinarith)
def reversal : ListReverse.Layouts w (K × V) where
  entry := layout.row
  capacity := layout.capacity
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := layout.fits_of_le (by rw [row_words]; dsimp only [width]; nlinarith)

include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (small : buffers ≤ 16) : body.program.savedBuffer < 2 ^ w := by
  have := layout.wordFits
  dsimp only [Realizer.savedBuffer]
  omega

end Layouts
end Signatures.Runtime.CaliperBackend.AttachRows
