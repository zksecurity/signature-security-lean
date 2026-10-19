import Signatures.Runtime.Caliper.LookupLayout
import Signatures.Runtime.Caliper.CompositionAcceptance

/-! Layouts for source-list indexing. The index and stored-list capacities are
independent bounds; neither ranges over the source value type. -/

namespace Signatures.Runtime.CaliperBackend.ListIndex
open Caliper BoundedSource

structure Layouts (w : Nat) (V : Type) where
  value : Layout w V
  capacity : Nat
  indexBound : Nat
  indexPositive : 0 < indexBound
  indexFits : indexBound ≤ 2 ^ w
  wordFits : 16 < 2 ^ w
  countFits : capacity < 2 ^ w
  storageFits : 8 * (3 + (capacity + 1) * value.representation.encoding.words) < 2 ^ w

namespace Layouts
variable {w : Nat} {V : Type} (layout : Layouts w V)

def width : Nat := 3 + (layout.capacity + 1) * layout.value.representation.encoding.words
theorem fits_of_le {words : Nat} (bound : words ≤ 8 * layout.width) : words < 2 ^ w := bound.trans_lt layout.storageFits
theorem value_le : layout.value.representation.encoding.words ≤ layout.width := by
  have := Nat.mul_le_mul_right layout.value.representation.encoding.words (show 1 ≤ layout.capacity + 1 by omega)
  dsimp only [width]; omega

def counter : Layout w Nat := Layout.counter w layout.indexBound (width_pos layout.wordFits) layout.indexFits
def boolean : Layout w Bool := DataImplementation.boolLayout w (width_pos layout.wordFits)
def unit (_layout : Layouts w V) : Layout w Unit := DataImplementation.unitLayout w
def list : Layout w (List V) := layout.value.boundedList layout.capacity layout.countFits
  (layout.fits_of_le (by dsimp only [width]; nlinarith))
def tail : Layout w (V × List V) := layout.value.prod layout.list
  (layout.fits_of_le (by change _ + (1 + layout.capacity * _) ≤ _; dsimp only [width]; nlinarith))
def input : Layout w (Nat × (V × List V)) := layout.counter.prod layout.tail
  (layout.fits_of_le (by change 1 + (_ + (1 + layout.capacity * _)) ≤ _; dsimp only [width]; nlinarith))
def payload : Layout w (Bool × V) := layout.boolean.prod layout.value
  (layout.fits_of_le (by change 1 + _ ≤ _; have := layout.value_le; dsimp only [width] at *; omega))
def state : Layout w (Nat × (Bool × V)) := layout.counter.prod layout.payload
  (layout.fits_of_le (by change 1 + (1 + _) ≤ _; have := layout.value_le; dsimp only [width] at *; omega))
def stateTail : Layout w ((Nat × (Bool × V)) × Unit) := layout.state.prod layout.unit
  (layout.fits_of_le (by change (1 + (1 + _)) + 0 ≤ _; dsimp only [width]; nlinarith))

theorem argFits : layout.value.representation.encoding.words + layout.state.representation.encoding.words + layout.unit.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by change _ + (1 + (1 + _)) + 0 ≤ _; dsimp only [width]; nlinarith)
theorem frameFits : 1 + layout.capacity * layout.value.representation.encoding.words + layout.state.representation.encoding.words +
    2 * layout.unit.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by change 1 + layout.capacity * _ + (1 + (1 + _)) + 2 * 0 ≤ _; dsimp only [width]; nlinarith)
def body := FoldImplementation.bodyInput layout.value layout.state layout.unit layout.argFits
def frame := FoldImplementation.input layout.value layout.state layout.unit layout.capacity layout.countFits layout.frameFits

@[simp] theorem counter_words : layout.counter.representation.encoding.words = 1 := rfl
@[simp] theorem boolean_words : layout.boolean.representation.encoding.words = 1 := rfl
@[simp] theorem unit_words : layout.unit.representation.encoding.words = 0 := rfl
@[simp] theorem list_words : layout.list.representation.encoding.words = 1 + layout.capacity * layout.value.representation.encoding.words := rfl
@[simp] theorem tail_words : layout.tail.representation.encoding.words = layout.value.representation.encoding.words + layout.list.representation.encoding.words := rfl
@[simp] theorem input_words : layout.input.representation.encoding.words = 2 + (layout.capacity + 1) * layout.value.representation.encoding.words := by
  change 1 + (_ + (1 + layout.capacity * _)) = _; ring
@[simp] theorem payload_words : layout.payload.representation.encoding.words = 1 + layout.value.representation.encoding.words := rfl
@[simp] theorem state_words : layout.state.representation.encoding.words = 2 + layout.value.representation.encoding.words := by
  change 1 + (1 + _) = _; omega
@[simp] theorem stateTail_words : layout.stateTail.representation.encoding.words = layout.state.representation.encoding.words := by
  change layout.state.representation.encoding.words + 0 = _; omega
@[simp] theorem body_words : layout.body.representation.encoding.words = 2 + 2 * layout.value.representation.encoding.words := by
  change _ + ((1 + (1 + _)) + 0) = _; omega
@[simp] theorem frame_words : layout.frame.representation.encoding.words = layout.width := by
  change (1 + layout.capacity * _) + ((1 + (1 + _)) + 0) = 3 + (layout.capacity + 1) * _; ring

theorem sizes : layout.input.representation.encoding.words ≤ layout.width ∧
    layout.state.representation.encoding.words ≤ layout.width ∧
    layout.body.representation.encoding.words ≤ 2 * layout.width ∧
    layout.list.representation.encoding.words ≤ layout.width ∧
    layout.tail.representation.encoding.words ≤ layout.width ∧
    layout.payload.representation.encoding.words ≤ layout.width := by
  simp only [input_words, state_words, body_words, list_words, tail_words, payload_words]
  dsimp only [width]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem bodyDuplicate : layout.body.representation.encoding.words + layout.body.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.sizes; omega)
theorem bodyTag : 1 + layout.body.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.sizes; dsimp only [width] at *; omega)

include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (small : buffers ≤ 16) : body.program.savedBuffer < 2 ^ w := by
  have := layout.wordFits
  dsimp only [Realizer.savedBuffer]
  omega

end Layouts
end Signatures.Runtime.CaliperBackend.ListIndex
