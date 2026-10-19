import Signatures.Runtime.Caliper.IndexLayout
import Signatures.Runtime.Caliper.EncodedConstant
import Signatures.Runtime.Index

/-! The actual list-index scan body. A found result is retained; a zero remaining
index selects the current entry; otherwise an executed saturating subtraction
decrements the counter. All projections and reconstructed states are charged. -/

namespace Signatures.Runtime.CaliperBackend.ListIndex
open Caliper BoundedSource

variable {w : Nat} {V : Type} (layout : Layouts w V)

def current : Implementation .unit layout.body layout.state (fun value => value.2.1) :=
  (Implementation.second (by decide) layout.value layout.stateTail layout.wordFits
    (by have := layout.argFits; change _ + (_ + _) < _; omega)).then
    (Implementation.first (by decide) layout.state layout.unit layout.wordFits layout.stateTail.representation.fits)
def entry : Implementation .unit layout.body layout.value Prod.fst :=
  Implementation.first (by decide) layout.value layout.stateTail layout.wordFits
    (by have := layout.argFits; change _ + (_ + _) < _; omega)
def remaining : Implementation .unit layout.body layout.counter (fun value => value.2.1.1) :=
  (current layout).then (Implementation.first (by decide) layout.counter layout.payload layout.wordFits layout.state.representation.fits)
def payload : Implementation .unit layout.body layout.payload (fun value => value.2.1.2) :=
  (current layout).then (Implementation.second (by decide) layout.counter layout.payload layout.wordFits layout.state.representation.fits)
def found : Implementation .unit layout.body layout.boolean (fun value => value.2.1.2.1) :=
  (payload layout).then (Implementation.first (by decide) layout.boolean layout.value layout.wordFits layout.payload.representation.fits)

theorem current_buffers : (current layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem entry_buffers : (entry layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem remaining_buffers : (remaining layout).program.code.memBound ≤ 2 := max_le (current_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem payload_buffers : (payload layout).program.code.memBound ≤ 2 := max_le (current_buffers layout) (Implementation.second_buffers _ _ _ _ _)
theorem found_buffers : (found layout).program.code.memBound ≤ 2 := max_le (payload_buffers layout) (Implementation.first_buffers _ _ _ _ _)

def zero : Implementation .unit layout.body layout.counter (fun _ => 0) :=
  Implementation.constant layout.body layout.counter ⟨0, layout.indexPositive⟩ layout.wordFits
def oneLayout : Layout w Nat := Layout.counter w 2 (width_pos layout.wordFits) (by have := layout.wordFits; omega)
def one : Implementation .unit layout.body (oneLayout layout) (fun _ => 1) :=
  Implementation.constant layout.body (oneLayout layout) ⟨1, by change 1 < 2; decide⟩ layout.wordFits
def yes : Implementation .unit layout.body layout.boolean (fun _ => true) :=
  Implementation.constant layout.body layout.boolean ⟨true, trivial⟩ layout.wordFits
theorem zero_buffers : (zero layout).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _
theorem one_buffers : (one layout).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _
theorem yes_buffers : (yes layout).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _

def zeroArgs : Implementation .unit layout.body
    (Natural.pair layout.indexBound layout.indexBound layout.wordFits layout.indexFits layout.indexFits)
    (fun value => (value.2.1.1, 0)) :=
  (remaining layout).pair (zero layout) (by decide) layout.wordFits
    (layout.nameFits _ (remaining_buffers layout) (by decide)) (layout.nameFits _ (zero_buffers layout) (by decide))
    layout.bodyDuplicate (layout.fits_of_le (by have := layout.sizes; rw [Layouts.counter_words]; dsimp only [Layouts.width] at *; omega))
    (by have := layout.wordFits; change 1 + 1 < _; omega)
def zeroTest : Implementation .unit layout.body layout.boolean (fun value => decide (value.2.1.1 = 0)) :=
  (zeroArgs layout).then (Natural.equal .unit layout.indexBound layout.indexBound layout.wordFits layout.indexFits layout.indexFits)

def subtractionArgs : Implementation .unit layout.body
    (Natural.pair layout.indexBound 2 layout.wordFits layout.indexFits (by have := layout.wordFits; omega))
    (fun value => (value.2.1.1, 1)) :=
  (remaining layout).pair (one layout) (by decide) layout.wordFits
    (layout.nameFits _ (remaining_buffers layout) (by decide)) (layout.nameFits _ (one_buffers layout) (by decide))
    layout.bodyDuplicate (layout.fits_of_le (by have := layout.sizes; rw [Layouts.counter_words]; dsimp only [Layouts.width] at *; omega))
    (by have := layout.wordFits; change 1 + 1 < _; omega)
def decrement : Implementation .unit layout.body layout.counter (fun value => value.2.1.1 - 1) :=
  (subtractionArgs layout).then (Natural.subtract .unit layout.indexBound 2 layout.wordFits layout.indexFits (by have := layout.wordFits; omega))

theorem zeroArgs_buffers : (zeroArgs layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _ (remaining_buffers layout) (zero_buffers layout)
theorem zeroTest_buffers : (zeroTest layout).program.code.memBound ≤ 3 := max_le (zeroArgs_buffers layout) (by change 1 ≤ 3; decide)
theorem subtractionArgs_buffers : (subtractionArgs layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _ (remaining_buffers layout) (one_buffers layout)
theorem decrement_buffers : (decrement layout).program.code.memBound ≤ 3 := max_le (subtractionArgs_buffers layout) (by change 1 ≤ 3; decide)

def selected : Implementation .unit layout.body layout.payload (fun value => (true, value.1)) :=
  (yes layout).pair (entry layout) (by decide) layout.wordFits
    (layout.nameFits _ (yes_buffers layout) (by decide)) (layout.nameFits _ (entry_buffers layout) (by decide))
    layout.bodyDuplicate (layout.fits_of_le (by have := layout.sizes; rw [Layouts.boolean_words]; dsimp only [Layouts.width] at *; omega))
    layout.payload.representation.fits
theorem selected_buffers : (selected layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _ (yes_buffers layout) (entry_buffers layout)
def hit : Implementation .unit layout.body layout.state (fun value => (0, true, value.1)) :=
  (zero layout).pair (selected layout) (by decide) layout.wordFits
    (layout.nameFits _ (zero_buffers layout) (by decide)) (layout.nameFits _ (selected_buffers layout) (by decide))
    layout.bodyDuplicate (layout.fits_of_le (by have := layout.sizes; rw [Layouts.counter_words]; dsimp only [Layouts.width] at *; omega))
    layout.state.representation.fits
def miss : Implementation .unit layout.body layout.state (fun value => (value.2.1.1 - 1, value.2.1.2)) :=
  (decrement layout).pair (payload layout) (by decide) layout.wordFits
    (layout.nameFits _ (decrement_buffers layout) (by decide)) (layout.nameFits _ (payload_buffers layout) (by decide))
    layout.bodyDuplicate (layout.fits_of_le (by have := layout.sizes; rw [Layouts.counter_words]; dsimp only [Layouts.width] at *; omega))
    layout.state.representation.fits
theorem hit_buffers : (hit layout).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 3) _ _ _ _ _ _ _ _ (zero_buffers layout) (selected_buffers layout)
theorem miss_buffers : (miss layout).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 3) (secondBuffers := 2) _ _ _ _ _ _ _ _ (decrement_buffers layout) (payload_buffers layout)

def searchCompiled := (zeroTest layout).checkedBranch (hw := layout.wordFits) (hit layout) (miss layout) (by decide) layout.bodyDuplicate layout.bodyTag
theorem search_accepted : (searchCompiled layout).isSome := by
  obtain ⟨implementation, equal, _⟩ := Implementation.checkedBranch_accept (zeroTest layout) (hit layout) (miss layout) (by decide)
    (zeroTest_buffers layout) (hit_buffers layout) (miss_buffers layout) (by have := layout.wordFits; omega) layout.bodyDuplicate layout.bodyTag
  rw [searchCompiled, equal]
  rfl
def search := (searchCompiled layout).get (search_accepted layout)
theorem search_buffers : (search layout).program.code.memBound ≤ 4 := by
  obtain ⟨implementation, equal, bound⟩ := Implementation.checkedBranch_accept (zeroTest layout) (hit layout) (miss layout) (by decide)
    (zeroTest_buffers layout) (hit_buffers layout) (miss_buffers layout) (by have := layout.wordFits; omega) layout.bodyDuplicate layout.bodyTag
  rw [show search layout = implementation from Option.get_of_eq_some (search_accepted layout) equal]
  exact bound

def bodyCompiled := (found layout).checkedBranch (hw := layout.wordFits) (current layout) (search layout) (by decide) layout.bodyDuplicate layout.bodyTag
theorem body_accepted : (bodyCompiled layout).isSome := by
  obtain ⟨implementation, equal, _⟩ := Implementation.checkedBranch_accept (found layout) (current layout) (search layout) (by decide)
    (found_buffers layout) (current_buffers layout) (search_buffers layout) (by have := layout.wordFits; omega) layout.bodyDuplicate layout.bodyTag
  rw [bodyCompiled, equal]
  rfl
def body : Implementation .unit layout.body layout.state (fun value => indexStep value.2.1 value.1) :=
  ((bodyCompiled layout).get (body_accepted layout)).castFunction (by
    funext value
    rcases value with ⟨entry, ⟨n, flag, saved⟩, _context⟩
    cases flag <;> simp [indexStep])
theorem body_buffers : (body layout).program.code.memBound ≤ 4 := by
  obtain ⟨implementation, equal, bound⟩ := Implementation.checkedBranch_accept (found layout) (current layout) (search layout) (by decide)
    (found_buffers layout) (current_buffers layout) (search_buffers layout) (by have := layout.wordFits; omega) layout.bodyDuplicate layout.bodyTag
  change ((bodyCompiled layout).get (body_accepted layout)).program.code.memBound ≤ 4
  rw [Option.get_of_eq_some (body_accepted layout) equal]
  exact bound

end Signatures.Runtime.CaliperBackend.ListIndex
