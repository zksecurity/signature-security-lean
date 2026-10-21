import Signatures.Runtime.Caliper.SchnorrROMTapeLayout
import Signatures.Runtime.Caliper.ConstructedArithmetic
import Signatures.Runtime.Caliper.ListIndexBounds

/-! The fresh-challenge rejection test reads the saved public-family cell at a
runtime slot. Private cells do not consume the slot. A missing slot is unequal,
so this test never substitutes the final forgery's challenge for the tape cell. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
open Caliper BoundedSource SchnorrROMTape
abbrev Accumulator := Nat × (Bool × Bool)
variable {w : Nat} {F : Type} (layout : Layouts w F)

theorem width_min : layout.scalar.representation.encoding.words + 6 ≤ layout.width := by
  unfold Layouts.width
  nlinarith

def flags := layout.boolean.prod layout.boolean
  (by have := layout.wordFits; change 1 + 1 < _; omega)
def state := layout.counter.prod (flags layout)
  (by have := layout.wordFits; change 1 + (1 + 1) < _; omega)
def tail := (state layout).prod layout.scalar (layout.fits_of_le (by
  change (1 + (1 + 1)) + _ ≤ _; unfold Layouts.width; nlinarith))
def inputTail := layout.scalar.prod (layout.list layout.capacity (by omega)) (layout.fits_of_le (by
  have := layout.list_le layout.capacity (by omega); unfold Layouts.width at *; nlinarith))
def input := layout.counter.prod (inputTail layout) (layout.fits_of_le (by
  change 1 + (_ + _) ≤ _; have := layout.list_le layout.capacity (by omega); unfold Layouts.width at *; nlinarith))
theorem argFits : layout.entry.representation.encoding.words + (state layout).representation.encoding.words +
    layout.scalar.representation.encoding.words < 2 ^ w := layout.fits_of_le (by
  change _ + 3 + _ ≤ _; rw [Layouts.entry_words]; unfold Layouts.width; nlinarith)
theorem frameFits : 1 + layout.capacity * layout.entry.representation.encoding.words + (state layout).representation.encoding.words +
    2 * layout.scalar.representation.encoding.words < 2 ^ w := layout.fits_of_le (by
  change 1 + layout.capacity * _ + 3 + 2 * _ ≤ _; rw [Layouts.entry_words]; unfold Layouts.width; nlinarith)
def body := FoldImplementation.bodyInput layout.entry (state layout) layout.scalar (argFits layout)
def frame := FoldImplementation.input layout.entry (state layout) layout.scalar layout.capacity
  (by have := layout.countFits; omega) (frameFits layout)
theorem sizes : (input layout).representation.encoding.words ≤ 2 * layout.width ∧
    (body layout).representation.encoding.words ≤ 2 * layout.width ∧
    (frame layout).representation.encoding.words ≤ 2 * layout.width := by
  have listSize := layout.list_le layout.capacity (by omega)
  have entrySize := layout.entry_le
  change (1 + (_ + _)) ≤ _ ∧ (_ + (3 + _)) ≤ _ ∧ (1 + layout.capacity * _ + (3 + _)) ≤ _
  rw [Layouts.entry_words] at *
  unfold Layouts.width at *
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
theorem duplicate : (body layout).representation.encoding.words + (body layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := sizes layout; omega)
theorem tagged : 1 + (body layout).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := sizes layout; unfold Layouts.width at *; omega)

def step [DecidableEq F] (value : Schnorr.TapeCell F × (Accumulator × F)) : Accumulator :=
  if value.2.1.2.1 = true then value.2.1
  else if value.1.1 = 1 then
    if value.2.1.1 = 0 then (0, true, decide (value.1.2.1 = value.2.2))
    else (value.2.1.1 - 1, false, false)
  else value.2.1

def publicValues (cells : List (Schnorr.TapeCell F)) : List F :=
  cells.filterMap (fun cell => if cell.1 = 1 then some cell.2.1 else none)

omit layout in
theorem publicValues_original [Zero F] (cells : List (Schnorr.TapeCell F)) :
    publicValues cells = Schnorr.RawTape.values (.inr ()) cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    simp only [Schnorr.RawTape.values] at ih
    by_cases tagged : cell.1 = 1
    all_goals simp [publicValues, Schnorr.RawTape.values, Schnorr.SeedTape.values,
      Schnorr.SeedTape.familyTag, Schnorr.decodeReply, tagged, ← ih]

omit layout in
theorem fold_found [DecidableEq F] (cells : List (Schnorr.TapeCell F)) (n : Nat) (matched : Bool) (answer : F) :
    cells.foldl (fun acc cell => step (cell, acc, answer)) (n, true, matched) = (n, true, matched) := by
  induction cells with
  | nil => rfl
  | cons cell cells ih => simpa only [List.foldl_cons, step, ↓reduceIte] using ih

omit layout in
theorem publicValues_cons (cell : Schnorr.TapeCell F) (cells : List (Schnorr.TapeCell F)) :
    publicValues (cell :: cells) = if cell.1 = 1 then cell.2.1 :: publicValues cells else publicValues cells := by
  simp only [publicValues, List.filterMap_cons]
  by_cases tagged : cell.1 = 1 <;> simp [tagged]

omit layout in
theorem fold_value [DecidableEq F] (cells : List (Schnorr.TapeCell F)) (n : Nat) (answer : F) :
    (cells.foldl (fun acc cell => step (cell, acc, answer)) (n, false, false)).2.2 =
      decide ((publicValues cells)[n]? = some answer) := by
  induction cells generalizing n with
  | nil => simp [publicValues]
  | cons cell cells ih =>
    rw [List.foldl_cons, publicValues_cons]
    by_cases tagged : cell.1 = 1
    · rw [ite_eq_left tagged]
      cases n with
      | zero =>
        rw [show step (cell, (0, false, false), answer) = (0, true, decide (cell.2.1 = answer)) by simp [step, tagged], fold_found]
        simp only [List.getElem?_cons_zero, Option.some.injEq]
      | succ n =>
        rw [show step (cell, (n + 1, false, false), answer) = (n, false, false) by simp [step, tagged], List.getElem?_cons_succ]
        exact ih n
    · rw [ite_eq_right tagged, show step (cell, (n, false, false), answer) = (n, false, false) by simp [step, tagged]]
      exact ih n

def source [DecidableEq F] (value : Nat × (F × List (Schnorr.TapeCell F))) : Bool :=
  decide ((publicValues value.2.2)[value.1]? = some value.2.1)

omit layout in
theorem source_original [Zero F] [DecidableEq F] (value : Nat × (F × List (Schnorr.TapeCell F))) :
    source value = decide ((Schnorr.RawTape.values (.inr ()) value.2.2)[value.1]? = some value.2.1) := by
  rw [source, publicValues_original]

end Signatures.Runtime.CaliperBackend.SchnorrROM.FreshGuard
