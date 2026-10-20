import Signatures.Runtime.Caliper.ListReverseBounds
import Signatures.Runtime.Caliper.CompositionAcceptance
import Signatures.Runtime.SchnorrRawTape

/-! Bounded storage for the original ROM replay cells. A cell contains its
oracle-family tag, scalar payload and natural payload. Natural values occupy
one word; scalar representations and tape capacity remain explicit. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape
open Caliper BoundedSource

structure Layouts (w : Nat) (F : Type) where
  scalar : Layout w F
  capacity : Nat
  wordFits : 16 < 2 ^ w
  countFits : capacity + 1 < 2 ^ w
  storageFits : 16 * (4 + (capacity + 2) * (scalar.representation.encoding.words + 2)) < 2 ^ w

namespace Layouts
variable {w : Nat} {F : Type} (layout : Layouts w F)

def width : Nat := 4 + (layout.capacity + 2) * (layout.scalar.representation.encoding.words + 2)
theorem fits_of_le {words : Nat} (bound : words ≤ 16 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits
def counter : Layout w Nat := Layout.counter w (2 ^ w) (width_pos layout.wordFits) le_rfl
def boolean : Layout w Bool := DataImplementation.boolLayout w (width_pos layout.wordFits)
def unit (_layout : Layouts w F) : Layout w Unit := DataImplementation.unitLayout w
def payload := layout.scalar.prod layout.counter
  (layout.fits_of_le (by change _ + 1 ≤ _; unfold width; nlinarith))
def entry : Layout w (Schnorr.TapeCell F) := layout.counter.prod layout.payload
  (layout.fits_of_le (by change 1 + (_ + 1) ≤ _; unfold width; nlinarith))
def list (n : Nat) (small : n ≤ layout.capacity + 1) : Layout w (List (Schnorr.TapeCell F)) :=
  layout.entry.boundedList n (small.trans_lt layout.countFits)
    (layout.fits_of_le (by
      change 1 + n * (1 + (layout.scalar.representation.encoding.words + 1)) ≤ _
      have := Nat.mul_le_mul_right (layout.scalar.representation.encoding.words + 2) small
      unfold width
      nlinarith))
def state (n : Nat) (small : n ≤ layout.capacity + 1) : Layout w (Nat × List (Schnorr.TapeCell F)) :=
  layout.counter.prod (layout.list n small) (layout.fits_of_le (by
    change 1 + (1 + n * (1 + (layout.scalar.representation.encoding.words + 1))) ≤ _
    have := Nat.mul_le_mul_right (layout.scalar.representation.encoding.words + 2) small
    unfold width
    nlinarith))
def states (i : Fin (layout.capacity + 1)) := layout.state i.val (by omega)
def stateTail (i : Fin (layout.capacity + 1)) := (layout.states i).prod layout.unit
  (by change (layout.states i).representation.encoding.words + 0 < _; simpa using (layout.states i).representation.fits)

@[simp] theorem counter_words : layout.counter.representation.encoding.words = 1 := rfl
@[simp] theorem boolean_words : layout.boolean.representation.encoding.words = 1 := rfl
@[simp] theorem unit_words : layout.unit.representation.encoding.words = 0 := rfl
@[simp] theorem entry_words : layout.entry.representation.encoding.words = layout.scalar.representation.encoding.words + 2 := by
  change 1 + (_ + 1) = _; omega
@[simp] theorem list_words (n : Nat) (small : n ≤ layout.capacity + 1) :
    (layout.list n small).representation.encoding.words = 1 + n * layout.entry.representation.encoding.words := rfl
@[simp] theorem state_words (n : Nat) (small : n ≤ layout.capacity + 1) :
    (layout.state n small).representation.encoding.words = 2 + n * layout.entry.representation.encoding.words := by
  change 1 + (1 + n * _) = _; omega
@[simp] theorem states_words (i : Fin (layout.capacity + 1)) :
    (layout.states i).representation.encoding.words = 2 + i.val * layout.entry.representation.encoding.words :=
  layout.state_words _ _

theorem entry_le : layout.entry.representation.encoding.words ≤ layout.width := by
  rw [entry_words]; unfold width; nlinarith
theorem list_le (n : Nat) (small : n ≤ layout.capacity + 1) :
    (layout.list n small).representation.encoding.words ≤ layout.width := by
  rw [list_words, entry_words]
  have := Nat.mul_le_mul_right (layout.scalar.representation.encoding.words + 2) small
  unfold width; nlinarith
theorem state_le (n : Nat) (small : n ≤ layout.capacity + 1) :
    (layout.state n small).representation.encoding.words ≤ layout.width := by
  rw [state_words, entry_words]
  have := Nat.mul_le_mul_right (layout.scalar.representation.encoding.words + 2) small
  unfold width; nlinarith

theorem argFits (i : Fin layout.capacity) :
    layout.entry.representation.encoding.words + (layout.states i.castSucc).representation.encoding.words +
      layout.unit.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by
    have := layout.entry_le; have := layout.state_le i.val (by omega)
    change _ + (layout.state i.val _).representation.encoding.words + 0 ≤ _
    omega)
theorem frameFits (i : Fin (layout.capacity + 1)) :
    1 + (layout.capacity - i.val) * layout.entry.representation.encoding.words +
      (layout.states i).representation.encoding.words + 2 * layout.unit.representation.encoding.words < 2 ^ w := by
  apply layout.fits_of_le
  rw [states_words, unit_words]
  have combined : (layout.capacity - i.val) * layout.entry.representation.encoding.words +
      i.val * layout.entry.representation.encoding.words = layout.capacity * layout.entry.representation.encoding.words := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  have := layout.list_le layout.capacity (by omega)
  rw [list_words] at this
  omega
def body (i : Fin layout.capacity) :=
  FoldImplementation.bodyInput layout.entry (layout.states i.castSucc) layout.unit (layout.argFits i)
def frame := FoldImplementation.input layout.entry (layout.states 0) layout.unit layout.capacity
  (by have := layout.countFits; omega) (layout.frameFits 0)

theorem body_le (i : Fin layout.capacity) : (layout.body i).representation.encoding.words ≤ 2 * layout.width := by
  change layout.entry.representation.encoding.words + ((layout.state i.val _).representation.encoding.words + 0) ≤ _
  have := layout.entry_le; have := layout.state_le i.val (by omega)
  omega
theorem bodyDuplicate (i : Fin layout.capacity) :
    (layout.body i).representation.encoding.words + (layout.body i).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.body_le i; omega)
theorem bodyTag (i : Fin layout.capacity) : 1 + (layout.body i).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.body_le i; unfold width at *; omega)

include layout in
theorem nameFits {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}
    (body : Implementation .unit input output f) {buffers : Nat}
    (bound : body.program.code.memBound ≤ buffers) (small : buffers ≤ 16) : body.program.savedBuffer < 2 ^ w := by
  have := layout.wordFits
  dsimp only [Realizer.savedBuffer]
  omega

def reverse : ListReverse.Layouts w (Schnorr.TapeCell F) where
  entry := layout.entry
  capacity := layout.capacity + 1
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := layout.fits_of_le (by rw [entry_words]; unfold width; nlinarith)

end Layouts
end Signatures.Runtime.CaliperBackend.SchnorrROMTape
