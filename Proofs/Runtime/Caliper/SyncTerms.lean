import Proofs.Runtime.Caliper.WeightedRowsLayout
import Proofs.Runtime.Caliper.SourceListData
import Proofs.Runtime.Caliper.SourceStructure
import Proofs.Runtime.Caliper.EncodedConstant
import Proofs.Runtime.Caliper.LayoutTools
import Proofs.Runtime.Caliper.StructuralBudgets
import Proofs.Runtime.Caliper.StructuralNames

/-! Executed term generators of the two synchronized PS weighted schemes. A message is a
period with a scalar, laid out exactly as a weighted term row, and each scheme's term list has
one row: scheme₁ pairs the period with the coefficient `1`, scheme₂ with the message scalar. -/
namespace Signatures.Runtime.CaliperBackend.SyncTerms
open Caliper BoundedSource

set_option linter.unusedSectionVars false

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom} {R : Type}
  (layout : CacheAccumulate.Layouts w (key.Value base) (val.Value base) R)
  (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
  (frameFits : 1 + (capacity + 4) * (WeightedRows.term layout).representation.encoding.words < 2 ^ w)

/-- Messages are laid out as term rows. -/
abbrev message : Layout w (key.Value base × val.Value base) := WeightedRows.term layout
include layout in
theorem wordFits : 16 < 2 ^ w := layout.cache.wordFits
include frameFits in
theorem storageFits : 1 + (capacity + 1) * (WeightedRows.term layout).representation.encoding.words < 2 ^ w := by
  have := frameFits; nlinarith
/-- The term list of capacity `capacity + 1`. -/
abbrev output : Layout w (List (key.Value base × val.Value base)) :=
  (WeightedRows.term layout).boundedList (capacity + 1) countFits (storageFits layout capacity frameFits)

theorem term_words : (WeightedRows.term layout).representation.encoding.words =
    layout.cache.key.representation.encoding.words + layout.coefficient.representation.encoding.words := rfl

def empty : Implementation .unit (message layout)
    ((WeightedRows.term layout).boundedList capacity (by omega) (by nlinarith)) (fun _ => []) :=
  Implementation.constant (message layout) ((WeightedRows.term layout).boundedList capacity (by omega) (by nlinarith))
    ⟨[], Nat.zero_le _, fun _ h => nomatch h⟩ (wordFits layout)

/-- A message as a one-row term list. -/
def single : Implementation .unit (message layout) (ListData.consInput (WeightedRows.term layout) capacity (wordFits layout) countFits
    (storageFits layout capacity frameFits)) (fun m => (m, [])) :=
  (Implementation.identity _ (width_pos (wordFits layout))).pair' (a := 0) (b := 2) (empty layout capacity countFits frameFits) (wordFits layout)
    (Implementation.identity_buffers _) (Implementation.constant_buffers _ _ _ _) (by have := wordFits layout; omega)
    (by change _ + _ + _ + (1 + capacity * _) < 2 ^ w; nlinarith)

def singleton : Implementation .unit (message layout) (output layout capacity countFits frameFits) (fun m => [m]) :=
  (single layout capacity countFits frameFits).then
    (ListData.cons .unit (by decide) (WeightedRows.term layout) capacity (wordFits layout) countFits (storageFits layout capacity frameFits))

variable [One (val.Value base)] (oneValid : layout.coefficient.valid 1)

/-- Scheme₁'s row `(t, 1)`. -/
def row₁ : Implementation .unit (message layout) (message layout) (fun m => (m.1, 1)) :=
  (Implementation.first (by decide) layout.cache.key layout.coefficient (wordFits layout) (WeightedRows.term layout).representation.fits).pair'
    (a := 2) (b := 2) (Implementation.constant (message layout) layout.coefficient ⟨1, oneValid⟩ (wordFits layout)) (wordFits layout)
    (Implementation.first_buffers _ _ _ _ _) (Implementation.constant_buffers _ _ _ _) (by have := wordFits layout; omega)
    (by
      show (WeightedRows.term layout).representation.encoding.words + (WeightedRows.term layout).representation.encoding.words +
        layout.cache.key.representation.encoding.words + layout.coefficient.representation.encoding.words < 2 ^ w
      have h := frameFits
      rw [term_words] at h ⊢
      nlinarith)

/-- Scheme₁: `[(t, 1)]`. -/
def generator₁ : Implementation .unit (message layout) (output layout capacity countFits frameFits) (fun m => [(m.1, 1)]) :=
  (row₁ layout capacity countFits frameFits oneValid).then (singleton layout capacity countFits frameFits)
/-- Scheme₂: `[(t, m)]`. -/
def generator₂ : Implementation .unit (message layout) (output layout capacity countFits frameFits) (fun m => [m]) :=
  singleton layout capacity countFits frameFits

/-! ## Budgets -/

/-- The row width and the list width. -/
abbrev unit : Nat := (WeightedRows.term layout).representation.encoding.words
abbrev listWidth : Nat := 1 + (capacity + 1) * unit layout
def timeBudget : Nat := 300 * listWidth layout capacity + 300 * unit layout
def codeBudget : Nat := 700 * listWidth layout capacity + 700 * unit layout

theorem single_boundedBy : (single layout capacity countFits frameFits).BoundedBy
    (24 + 24 * (capacity * unit layout) + 88 * unit layout) (217 + 78 * (capacity * unit layout) + 286 * unit layout) := by
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.identity_boundedBy _ _)
    (Implementation.constant_bounded' _ _ (le_refl (1 + capacity * unit layout))) (le_refl _) (le_refl _) (le_refl _)).mono ?_ ?_
  all_goals simp only [Layout.boundedList_words]; nlinarith

theorem singleton_boundedBy : (singleton layout capacity countFits frameFits).BoundedBy
    (24 + 24 * (capacity * unit layout) + 88 * unit layout + (8 * listWidth layout capacity + 5))
    (217 + 78 * (capacity * unit layout) + 286 * unit layout + (26 * listWidth layout capacity + 38) + 1) :=
  (single_boundedBy layout capacity countFits frameFits).then (ListData.cons_boundedBy _ _ _ _ _)

theorem row₁_boundedBy : (row₁ layout capacity countFits frameFits oneValid).BoundedBy (120 * unit layout) (390 * unit layout + 152) := by
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (Implementation.first_boundedBy' _ _ (le_refl _))
    (Implementation.constant_bounded' _ _ (le_refl _)) (le_refl (unit layout)) (le_refl _) (le_refl _)).mono ?_ ?_
  all_goals
    have hf : unit layout = layout.cache.key.representation.encoding.words + layout.coefficient.representation.encoding.words := rfl
    omega

theorem generator₁_boundedBy : (generator₁ layout capacity countFits frameFits oneValid).BoundedBy
    (timeBudget layout capacity) (codeBudget layout capacity) := by
  refine ((row₁_boundedBy layout capacity countFits frameFits oneValid).then (singleton_boundedBy layout capacity countFits frameFits)).mono ?_ ?_
  all_goals
    have hL : listWidth layout capacity = 1 + (capacity + 1) * unit layout := rfl
    simp only [timeBudget, codeBudget]
    nlinarith [Nat.zero_le (unit layout), Nat.zero_le capacity]

theorem generator₂_boundedBy : (generator₂ layout capacity countFits frameFits).BoundedBy
    (timeBudget layout capacity) (codeBudget layout capacity) := by
  refine (singleton_boundedBy layout capacity countFits frameFits).mono ?_ ?_
  all_goals
    have hL : listWidth layout capacity = 1 + (capacity + 1) * unit layout := rfl
    simp only [timeBudget, codeBudget]
    nlinarith [Nat.zero_le (unit layout), Nat.zero_le capacity]

theorem singleton_names (slots : Nat) : NamesAccounted (singleton layout capacity countFits frameFits).program.code slots :=
  Implementation.then_names _ _
    (Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.identity_names _ _) (Implementation.constant_names _ _ _ _ _))
    (ListData.cons_names _ _ _ _ _ _)
theorem generator₁_names (slots : Nat) : NamesAccounted (generator₁ layout capacity countFits frameFits oneValid).program.code slots :=
  Implementation.then_names _ _
    (Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ _) (Implementation.constant_names _ _ _ _ _))
    (singleton_names layout capacity countFits frameFits slots)
theorem generator₂_names (slots : Nat) : NamesAccounted (generator₂ layout capacity countFits frameFits).program.code slots :=
  singleton_names layout capacity countFits frameFits slots

end Signatures.Runtime.CaliperBackend.SyncTerms
