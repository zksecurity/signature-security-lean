import Proofs.Runtime.Caliper.AttachLayout

/-! A complete executed attachment step. The coefficient scan is the constructed
ListIndex program; the new row is copied into a growing list and the source
counter is incremented by actual word arithmetic with a proved no-wrap bound. -/

namespace Signatures.Runtime.CaliperBackend.AttachRows
open Caliper BoundedSource
variable {w : Nat} {K V : Type} (layout : Layouts w K V) (i : Fin layout.capacity)

def key : Implementation .unit (layout.body i) layout.key Prod.fst :=
  Implementation.first (by decide) layout.key (layout.context i) layout.wordFits (layout.body i).representation.fits
def current : Implementation .unit (layout.body i) (layout.states i.castSucc) (fun value => value.2.1) :=
  (Implementation.second (by decide) layout.key (layout.context i) layout.wordFits (layout.body i).representation.fits).then
    (Implementation.first (by decide) (layout.states i.castSucc) layout.env layout.wordFits (layout.context i).representation.fits)
def counter : Implementation .unit (layout.body i) (layout.counter i.castSucc) (fun value => value.2.1.1) :=
  (current layout i).then (Implementation.first (by decide) (layout.counter i.castSucc) (layout.rows i.castSucc)
    layout.wordFits (layout.states i.castSucc).representation.fits)
def previous : Implementation .unit (layout.body i) (layout.rows i.castSucc) (fun value => value.2.1.2) :=
  (current layout i).then (Implementation.second (by decide) (layout.counter i.castSucc) (layout.rows i.castSucc)
    layout.wordFits (layout.states i.castSucc).representation.fits)
def environment : Implementation .unit (layout.body i) layout.env (fun value => value.2.2) :=
  (Implementation.second (by decide) layout.key (layout.context i) layout.wordFits (layout.body i).representation.fits).then
    (Implementation.second (by decide) (layout.states i.castSucc) layout.env layout.wordFits (layout.context i).representation.fits)
theorem key_buffers : (key layout i).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem current_buffers : (current layout i).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.first_buffers _ _ _ _ _)
theorem counter_buffers : (counter layout i).program.code.memBound ≤ 2 :=
  max_le (current_buffers layout i) (Implementation.first_buffers _ _ _ _ _)
theorem previous_buffers : (previous layout i).program.code.memBound ≤ 2 :=
  max_le (current_buffers layout i) (Implementation.second_buffers _ _ _ _ _)
theorem environment_buffers : (environment layout i).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers _ _ _ _ _) (Implementation.second_buffers _ _ _ _ _)
theorem Layouts.bodyDuplicate : (layout.body i).representation.encoding.words + (layout.body i).representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.body_size i; omega)

def lookupInput : Implementation .unit (layout.body i) (layout.indexing i).input (fun value => (value.2.1.1, value.2.2)) :=
  (counter layout i).pair (environment layout i) (by decide) layout.wordFits
    (layout.nameFits _ (counter_buffers layout i) (by decide)) (layout.nameFits _ (environment_buffers layout i) (by decide))
    (layout.bodyDuplicate i) (layout.fits_of_le (by rw [Layouts.counter_words]; have := layout.body_size i; dsimp only [Layouts.width] at *; omega))
    (layout.indexing i).input.representation.fits
def coefficient := (lookupInput layout i).then (ListIndex.implementation (layout.indexing i))
theorem lookupInput_buffers : (lookupInput layout i).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _ (counter_buffers layout i) (environment_buffers layout i)
theorem coefficient_buffers : (coefficient layout i).program.code.memBound ≤ 6 :=
  max_le ((lookupInput_buffers layout i).trans (by decide)) (ListIndex.buffers _)
def row : Implementation .unit (layout.body i) layout.row
    (fun value => (value.1, (value.2.2.2[value.2.1.1]?).getD value.2.2.1)) :=
  (key layout i).pair (coefficient layout i) (by decide) layout.wordFits
    (layout.nameFits _ (key_buffers layout i) (by decide)) (layout.nameFits _ (coefficient_buffers layout i) (by decide))
    (layout.bodyDuplicate i) (layout.fits_of_le (by have := layout.body_size i; have := layout.base_sizes; omega))
    layout.row.representation.fits
theorem row_buffers : (row layout i).program.code.memBound ≤ 7 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 6) _ _ _ _ _ _ _ _ (key_buffers layout i) (coefficient_buffers layout i)
def consInput : Layout w ((K × V) × List (K × V)) :=
  ListData.consInput layout.row i.val layout.wordFits (by have := layout.countFits; omega)
    (layout.rows i.succ).representation.fits
def consArgs : Implementation .unit (layout.body i) (consInput layout i)
    (fun value => ((value.1, (value.2.2.2[value.2.1.1]?).getD value.2.2.1), value.2.1.2)) :=
  (row layout i).pair (previous layout i) (by decide) layout.wordFits
    (layout.nameFits _ (row_buffers layout i) (by decide)) (layout.nameFits _ (previous_buffers layout i) (by decide))
    (layout.bodyDuplicate i) (layout.fits_of_le (by have := layout.body_size i; have := layout.base_sizes; omega))
    (consInput layout i).representation.fits
def updated : Implementation .unit (layout.body i) (layout.rows i.succ)
    (fun value => (value.1, (value.2.2.2[value.2.1.1]?).getD value.2.2.1) :: value.2.1.2) :=
  (consArgs layout i).then (ListData.cons .unit (by decide) layout.row i.val layout.wordFits
    (by have := layout.countFits; omega) (layout.rows i.succ).representation.fits)
theorem consArgs_buffers : (consArgs layout i).program.code.memBound ≤ 8 :=
  Implementation.pair_buffers (firstBuffers := 7) (secondBuffers := 2) _ _ _ _ _ _ _ _ (row_buffers layout i) (previous_buffers layout i)
theorem updated_buffers : (updated layout i).program.code.memBound ≤ 8 :=
  max_le (consArgs_buffers layout i) ((ListReverse.body_buffers (layout.reversal) i).trans (by decide))

def oneLayout : Layout w Nat := Layout.counter w 2 (width_pos layout.wordFits) (by have := layout.wordFits; omega)
def one : Implementation .unit (layout.body i) (oneLayout layout) (fun _ => 1) :=
  Implementation.constant (layout.body i) (oneLayout layout) ⟨1, by change 1 < 2; decide⟩ layout.wordFits
theorem one_buffers : (one layout i).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _
def addArgs : Implementation .unit (layout.body i)
    (Natural.pair (i.val + 1) 2 layout.wordFits (by have := layout.counterFits; omega) (by have := layout.wordFits; omega))
    (fun value => (value.2.1.1, 1)) :=
  (counter layout i).pair (one layout i) (by decide) layout.wordFits
    (layout.nameFits _ (counter_buffers layout i) (by decide)) (layout.nameFits _ (one_buffers layout i) (by decide))
    (layout.bodyDuplicate i) (layout.fits_of_le (by rw [Layouts.counter_words]; have := layout.body_size i; dsimp only [Layouts.width] at *; omega))
    (by change 1 + 1 < _; have := layout.wordFits; omega)
def advanced := (addArgs layout i).then (Natural.add .unit (i.val + 1) 2 layout.wordFits (by have := layout.counterFits; omega))
def advance : Implementation .unit (layout.body i) (layout.counter i.succ) (fun value => value.2.1.1 + 1) where
  preserves value valid := by
    have bound : value.2.1.1 < i.val + 1 := valid.2.1.1
    change value.2.1.1 + 1 < (i.val + 1) + 1
    omega
  program := (advanced layout i).program.viewOutput _ _ (fun _ => rfl)
theorem addArgs_buffers : (addArgs layout i).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _ (counter_buffers layout i) (one_buffers layout i)
theorem advance_buffers : (advance layout i).program.code.memBound ≤ 3 :=
  max_le (addArgs_buffers layout i) (by change 1 ≤ 3; decide)

def step (value : K × ((Nat × List (K × V)) × (V × List V))) : Nat × List (K × V) :=
  AGM.attachStep value.2.2.1 value.2.2.2 value.2.1 value.1
def body : Implementation .unit (layout.body i) (layout.states i.succ) step :=
  (advance layout i).pair (updated layout i) (by decide) layout.wordFits
    (layout.nameFits _ (advance_buffers layout i) (by decide)) (layout.nameFits _ (updated_buffers layout i) (by decide))
    (layout.bodyDuplicate i) (layout.fits_of_le (by rw [Layouts.counter_words]; have := layout.body_size i; dsimp only [Layouts.width] at *; omega))
    (layout.states i.succ).representation.fits
theorem body_buffers : (body layout i).program.code.memBound ≤ 9 :=
  Implementation.pair_buffers (firstBuffers := 3) (secondBuffers := 8) _ _ _ _ _ _ _ _ (advance_buffers layout i) (updated_buffers layout i)

end Signatures.Runtime.CaliperBackend.AttachRows
