import Proofs.Runtime.Caliper.ExpressionMemory

/-! Bounded layouts for the original association-list lookup. The capacity is
the number of stored entries, not the size of the key domain. A single explicit
storage condition supplies the internal copying and traversal-frame bounds. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

variable {w : Nat} {A B : Type}

@[simp] theorem Layout.prod_words (left : Layout w A) (right : Layout w B)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    (left.prod right fits).representation.encoding.words =
      left.representation.encoding.words + right.representation.encoding.words := rfl

@[simp] theorem Layout.boundedList_words (entry : Layout w A) (capacity : Nat)
    (countFits : capacity < 2 ^ w) (fits : 1 + capacity * entry.representation.encoding.words < 2 ^ w) :
    (entry.boundedList capacity countFits fits).representation.encoding.words =
      1 + capacity * entry.representation.encoding.words := rfl

structure LookupLayout (w : Nat) (K V : Type) where
  key : Layout w K
  value : Layout w V
  capacity : Nat
  wordFits : 16 < 2 ^ w
  countFits : capacity < 2 ^ w
  storageFits : 8 * (1 + capacity * (key.representation.encoding.words + value.representation.encoding.words) +
    key.representation.encoding.words + value.representation.encoding.words) < 2 ^ w

namespace LookupLayout

variable {K V : Type} (layout : LookupLayout w K V)

def width : Nat := 1 + layout.capacity * (layout.key.representation.encoding.words + layout.value.representation.encoding.words) +
  layout.key.representation.encoding.words + layout.value.representation.encoding.words

theorem fits_of_le {words : Nat} (bound : words ≤ 8 * layout.width) : words < 2 ^ w :=
  bound.trans_lt layout.storageFits

def entry : Layout w (K × V) := layout.key.prod layout.value
  (layout.fits_of_le (by dsimp [width]; omega))

@[simp] theorem entry_words : layout.entry.representation.encoding.words =
    layout.key.representation.encoding.words + layout.value.representation.encoding.words := rfl

def table : Layout w (List (K × V)) := layout.entry.boundedList layout.capacity layout.countFits
  (layout.fits_of_le (by simp only [entry_words]; dsimp [width]; omega))

@[simp] theorem table_words : layout.table.representation.encoding.words =
    1 + layout.capacity * (layout.key.representation.encoding.words + layout.value.representation.encoding.words) := rfl

def unit (_layout : LookupLayout w K V) : Layout w Unit := DataImplementation.unitLayout w
@[simp] theorem unit_words : layout.unit.representation.encoding.words = 0 := rfl

def boolean : Layout w Bool := DataImplementation.boolLayout w (width_pos layout.wordFits)
@[simp] theorem boolean_words : layout.boolean.representation.encoding.words = 1 := rfl

def tableTail : Layout w (List (K × V) × Unit) := layout.table.prod layout.unit
  (layout.fits_of_le (by simp only [table_words, unit_words]; dsimp [width]; omega))

@[simp] theorem tableTail_words : layout.tableTail.representation.encoding.words = layout.table.representation.encoding.words := by
  simp [tableTail]

def valueTail : Layout w (V × (List (K × V) × Unit)) := layout.value.prod layout.tableTail
  (layout.fits_of_le (by simp only [tableTail_words, table_words]; dsimp [width]; omega))

@[simp] theorem valueTail_words : layout.valueTail.representation.encoding.words =
    layout.value.representation.encoding.words + layout.table.representation.encoding.words := by simp [valueTail]

def input : Layout w (K × (V × (List (K × V) × Unit))) := layout.key.prod layout.valueTail
  (layout.fits_of_le (by simp only [valueTail_words, table_words]; dsimp [width]; omega))

@[simp] theorem input_words : layout.input.representation.encoding.words = layout.width := by
  simp [input, width]
  omega

def result : Layout w (Bool × V) := layout.boolean.prod layout.value
  (layout.fits_of_le (by simp only [boolean_words]; dsimp [width]; omega))

@[simp] theorem result_words : layout.result.representation.encoding.words = 1 + layout.value.representation.encoding.words := rfl

def accumulatorTail : Layout w ((Bool × V) × (K × (V × (List (K × V) × Unit)))) :=
  layout.result.prod layout.input (layout.fits_of_le (by simp only [result_words, input_words]; dsimp [width]; omega))

@[simp] theorem accumulatorTail_words : layout.accumulatorTail.representation.encoding.words =
    1 + layout.value.representation.encoding.words + layout.width := by simp [accumulatorTail]

theorem argumentFits : layout.entry.representation.encoding.words + layout.result.representation.encoding.words +
    layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by simp only [entry_words, result_words, input_words]; dsimp [width]; omega)

def body : Layout w ((K × V) × ((Bool × V) × (K × (V × (List (K × V) × Unit))))) :=
  FoldImplementation.bodyInput layout.entry layout.result layout.input layout.argumentFits

@[simp] theorem body_words : layout.body.representation.encoding.words =
    layout.key.representation.encoding.words + layout.value.representation.encoding.words +
      (1 + layout.value.representation.encoding.words + layout.width) := by
  change _ + (_ + layout.input.representation.encoding.words) = _
  rw [input_words]
  rfl

theorem frameFits : 1 + layout.capacity * layout.entry.representation.encoding.words +
    layout.result.representation.encoding.words + 2 * layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by simp only [entry_words, result_words, input_words]; dsimp [width]; omega)

theorem body_duplicateFits : layout.body.representation.encoding.words + layout.body.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by simp only [body_words]; dsimp [width]; omega)

theorem body_tagFits : 1 + layout.body.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by simp only [body_words]; dsimp [width]; omega)

theorem input_duplicateFits : layout.input.representation.encoding.words + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by simp only [input_words]; omega)

theorem input_booleanFits : 1 + layout.input.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by simp only [input_words]; dsimp [width]; omega)

theorem keyPairFits : layout.key.representation.encoding.words + layout.key.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by dsimp [width]; omega)

end LookupLayout
end Signatures.Runtime.CaliperBackend.BoundedSource
