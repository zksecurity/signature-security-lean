import Signatures.Runtime.Caliper.SchnorrROMTapeTrim

/-! Executed replay reset from a selected slot, replacement cell and retained
tape. The scan builds its result backwards, reversal restores the source order,
and a charged duplication installs separate saved and remaining tapes. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

namespace Layouts
def resetTail := layout.entry.prod (layout.list layout.capacity (by omega))
  (layout.fits_of_le (by have := layout.entry_le; have := layout.list_le layout.capacity (by omega); omega))
def resetInput := layout.counter.prod layout.resetTail (layout.fits_of_le (by
  change 1 + (layout.entry.representation.encoding.words + (layout.list layout.capacity _).representation.encoding.words) ≤ _
  have := layout.entry_le; have := layout.list_le layout.capacity (by omega)
  unfold width at *; omega))
theorem resetInput_le : layout.resetInput.representation.encoding.words ≤ 2 * layout.width := by
  change 1 + (layout.entry.representation.encoding.words + (1 + layout.capacity * layout.entry.representation.encoding.words)) ≤ _
  rw [entry_words]; unfold width; nlinarith
theorem resetTail_le : layout.resetTail.representation.encoding.words ≤ 2 * layout.width := by
  have := layout.resetInput_le
  change 1 + layout.resetTail.representation.encoding.words ≤ _ at this
  omega
theorem resetDuplicate : layout.resetInput.representation.encoding.words + layout.resetInput.representation.encoding.words < 2 ^ w :=
  layout.fits_of_le (by have := layout.resetInput_le; omega)
def tapes := (layout.list (layout.capacity + 1) (by omega)).prod (layout.list (layout.capacity + 1) (by omega))
  (layout.fits_of_le (by have := layout.list_le (layout.capacity + 1) (by omega); omega))
def replay : Layout w (Schnorr.RawTape.State F) where
  valid state := layout.tapes.valid (state.saved, state.remaining)
  representation := layout.tapes.representation.transport
    { toFun := fun value => ⟨(value.val.saved, value.val.remaining), value.property⟩
      invFun := fun value => ⟨⟨value.val.1, value.val.2⟩, value.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end Layouts

def inputSlot : Implementation .unit layout.resetInput layout.counter Prod.fst :=
  Implementation.first (by decide) layout.counter layout.resetTail layout.wordFits layout.resetInput.representation.fits
def inputTail : Implementation .unit layout.resetInput layout.resetTail Prod.snd :=
  Implementation.second (by decide) layout.counter layout.resetTail layout.wordFits layout.resetInput.representation.fits
def inputAnswer : Implementation .unit layout.resetInput layout.entry (fun value => value.2.1) :=
  (inputTail layout).then (Implementation.first (by decide) layout.entry (layout.list layout.capacity (by omega))
    layout.wordFits layout.resetTail.representation.fits)
def inputList : Implementation .unit layout.resetInput (layout.list layout.capacity (by omega)) (fun value => value.2.2) :=
  (inputTail layout).then (Implementation.second (by decide) layout.entry (layout.list layout.capacity (by omega))
    layout.wordFits layout.resetTail.representation.fits)
def empty : Implementation .unit layout.resetInput (layout.list 0 (by omega)) (fun _ => []) :=
  Implementation.constant layout.resetInput (layout.list 0 (by omega)) ⟨[], by exact ⟨by simp, by simp⟩⟩ layout.wordFits
theorem inputSlot_buffers : (inputSlot layout).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem inputTail_buffers : (inputTail layout).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem inputAnswer_buffers : (inputAnswer layout).program.code.memBound ≤ 2 :=
  max_le (inputTail_buffers layout) (Implementation.first_buffers _ _ _ _ _)
theorem inputList_buffers : (inputList layout).program.code.memBound ≤ 2 :=
  max_le (inputTail_buffers layout) (Implementation.second_buffers _ _ _ _ _)
theorem empty_buffers : (empty layout).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _

def initialState : Implementation .unit layout.resetInput (layout.states 0) (fun value => (value.1, [])) :=
  (inputSlot layout).pair (empty layout) (by decide) layout.wordFits
    (layout.nameFits _ (inputSlot_buffers layout) (by decide)) (layout.nameFits _ (empty_buffers layout) (by decide))
    layout.resetDuplicate
    (layout.fits_of_le (by rw [Layouts.counter_words]; have := layout.resetInput_le; unfold Layouts.width at *; omega))
    (layout.states 0).representation.fits
theorem initialState_buffers : (initialState layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 2) _ _ _ _ _ _ _ _
    (inputSlot_buffers layout) (empty_buffers layout)
def initial : Implementation .unit layout.resetInput (layout.stateTail 0) (fun value => ((value.1, []), ())) where
  preserves value valid := ⟨(initialState layout).preserves value valid, trivial⟩
  program := (initialState layout).program.viewOutput _ _ (by
    intro value
    change _ ++ [] = _
    rw [List.append_nil]
    rfl)
def prepare : Implementation .unit layout.resetInput layout.frame (fun value => (value.2.2, (value.1, []), ())) :=
  (inputList layout).pair (initial layout) (by decide) layout.wordFits
    (layout.nameFits _ (inputList_buffers layout) (by decide)) (layout.nameFits _ (initialState_buffers layout) (by decide))
    layout.resetDuplicate
    (layout.fits_of_le (by have := layout.list_le layout.capacity (by omega); have := layout.resetInput_le; omega))
    layout.frame.representation.fits
theorem prepare_buffers : (prepare layout).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 3) _ _ _ _ _ _ _ _
    (inputList_buffers layout) (initialState_buffers layout)
def trimmed : Implementation .unit layout.resetInput (layout.list layout.capacity (by omega))
    (fun value => (Schnorr.SeedTape.trim 1 value.1 value.2.2).2.reverse) :=
  (((prepare layout).then (loop layout)).then
    (Implementation.second (by decide) layout.counter (layout.list layout.capacity (by omega)) layout.wordFits
      (layout.state layout.capacity (by omega)).representation.fits)).castFunction (by
        funext value
        change (FoldImplementation.sourceFold step (value.2.2, (value.1, []), ())).2 = _
        rw [loop_source])
theorem trimmed_buffers : (trimmed layout).program.code.memBound ≤ 5 :=
  max_le (max_le ((prepare_buffers layout).trans (by decide)) (loop_buffers layout))
    ((Implementation.second_buffers _ _ _ _ _).trans (by decide))

def prepend : Implementation .unit layout.resetInput
    (ListData.consInput layout.entry layout.capacity layout.wordFits layout.countFits
      (layout.list (layout.capacity + 1) (by omega)).representation.fits)
    (fun value => (value.2.1, (Schnorr.SeedTape.trim 1 value.1 value.2.2).2.reverse)) :=
  (inputAnswer layout).pair (trimmed layout) (by decide) layout.wordFits
    (layout.nameFits _ (inputAnswer_buffers layout) (by decide)) (layout.nameFits _ (trimmed_buffers layout) (by decide))
    layout.resetDuplicate
    (layout.fits_of_le (by have := layout.entry_le; have := layout.resetInput_le; omega)) _
theorem prepend_buffers : (prepend layout).program.code.memBound ≤ 6 :=
  Implementation.pair_buffers (firstBuffers := 2) (secondBuffers := 5) _ _ _ _ _ _ _ _
    (inputAnswer_buffers layout) (trimmed_buffers layout)

def resetList : Implementation .unit layout.resetInput (layout.list (layout.capacity + 1) (by omega))
    (fun value => Schnorr.SeedTape.reset 1 value.1 value.2.1 value.2.2) :=
  (((prepend layout).then (ListData.cons .unit (by decide) layout.entry layout.capacity layout.wordFits layout.countFits
    (layout.list (layout.capacity + 1) (by omega)).representation.fits)).then
      (ListReverse.implementation layout.reverse)).castFunction (by
        funext value
        change (value.2.1 :: (Schnorr.SeedTape.trim 1 value.1 value.2.2).2.reverse).reverse = _
        simp only [List.reverse_cons, List.reverse_reverse, Schnorr.SeedTape.reset])
theorem resetList_buffers : (resetList layout).program.code.memBound ≤ 6 :=
  max_le (max_le (prepend_buffers layout)
    ((ListReverse.body_buffers layout.reverse ⟨layout.capacity, by change layout.capacity < layout.capacity + 1; omega⟩).trans (by decide)))
    ((ListReverse.buffers layout.reverse).trans (by decide))

def duplicate : Implementation .unit (layout.list (layout.capacity + 1) (by omega)) layout.replay Schnorr.LazySeed.State.fromTape where
  preserves _ valid := ⟨valid, valid⟩
  program := (duplicateRealizer .unit (by decide) (layout.list (layout.capacity + 1) (by omega)).representation
    layout.wordFits layout.tapes.representation.fits).viewOutput _ _ (fun _ => rfl)
def implementation : Implementation .unit layout.resetInput layout.replay
    (fun value => Schnorr.LazySeed.State.fromTape (Schnorr.SeedTape.reset 1 value.1 value.2.1 value.2.2)) :=
  (resetList layout).then (duplicate layout)
theorem duplicate_buffers : (duplicate layout).program.code.memBound ≤ 2 :=
  (Assembly.code_names
    (Assembly.reads 0 0 (layout.list (layout.capacity + 1) (by omega)).representation.encoding.words ++
      Assembly.reads 0 0 (layout.list (layout.capacity + 1) (by omega)).representation.encoding.words) 1
    ((Assembly.sourcesBound_append _ _ _).mpr
      ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).2
theorem buffers : (implementation layout).program.code.memBound ≤ 6 :=
  max_le (resetList_buffers layout) ((duplicate_buffers layout).trans (by decide))

/-- The replacement packet is the actual challenge cell used by the existing
ROM reduction. The old remaining tape is discarded exactly as in `restart`. -/
theorem source [Zero F] (slot : Nat) (answer : F) (state : Schnorr.RawTape.State F) :
    Schnorr.LazySeed.State.fromTape (Schnorr.SeedTape.reset 1 slot (1, answer, 0) state.saved) =
      Schnorr.RawTape.restart slot answer state := rfl

end Signatures.Runtime.CaliperBackend.SchnorrROMTape
