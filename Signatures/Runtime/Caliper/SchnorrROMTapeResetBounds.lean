import Signatures.Runtime.Caliper.SchnorrROMTapeReset
import Signatures.Runtime.Caliper.ImplementationMemory

/-! Complete time, stored-code and memory bounds for replay reset. Both copies
of the installed tape and all memory visited during scanning are charged. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

theorem inputSlot_bounded : (inputSlot layout).BoundedBy 8 40 := Implementation.first_boundedBy _ _ _ _
theorem inputTail_bounded : (inputTail layout).BoundedBy (16 * layout.width) (52 * layout.width + 14) :=
  (Implementation.second_boundedBy _ _ _ _).mono
    (by have := layout.resetTail_le; omega) (by have := layout.resetTail_le; omega)
theorem inputAnswer_bounded : (inputAnswer layout).BoundedBy (24 * layout.width) (78 * layout.width + 29) := by
  apply ((inputTail_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals have := layout.entry_le; omega
theorem inputList_bounded : (inputList layout).BoundedBy (24 * layout.width) (78 * layout.width + 29) := by
  apply ((inputTail_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals have := layout.list_le layout.capacity (by omega); omega
theorem empty_bounded : (empty layout).BoundedBy 8 40 := by
  apply (Implementation.constant_bounded layout.resetInput (layout.list 0 (by omega))
    ⟨[], by exact ⟨by simp, by simp⟩⟩ layout.wordFits).mono
  · change 8 * (1 + 0 * layout.entry.representation.encoding.words) ≤ 8; simp
  · change 26 * (1 + 0 * layout.entry.representation.encoding.words) + 14 ≤ 40; simp
theorem initialState_bounded : (initialState layout).BoundedBy (104 * layout.width + 68) (338 * layout.width + 373) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (inputSlot_bounded layout) (empty_bounded layout)).mono
  all_goals
    simp only [Layouts.counter_words, Layouts.list_words, Nat.zero_mul, Nat.add_zero]
    have := layout.resetInput_le
    omega
theorem initial_bounded : (initial layout).BoundedBy (104 * layout.width + 68) (338 * layout.width + 373) :=
  ⟨(initialState_bounded layout).time_le, (initialState_bounded layout).code_le⟩
theorem prepare_bounded : (prepare layout).BoundedBy (300 * layout.width + 150) (1000 * layout.width + 700) := by
  apply (Implementation.pair_boundedBy (inputList layout) (initial layout) _ _ _ _ _ _
    (inputList_bounded layout) (initial_bounded layout)).mono
  all_goals
    have initialSize : (layout.stateTail 0).representation.encoding.words = 2 := by
      change (1 + (1 + 0 * layout.entry.representation.encoding.words)) + 0 = 2; omega
    rw [initialSize]
    have := layout.resetInput_le
    have := layout.list_le layout.capacity (by omega)
    omega
theorem trimmed_bounded : (trimmed layout).BoundedBy
    (308 * layout.width + 150 + loopTime layout) (1026 * layout.width + 716 + loopWords layout) := by
  apply (((prepare_bounded layout).then (loop_bounded layout)).then (Implementation.second_boundedBy _ _ _ _)).castFunction _ |>.mono
  all_goals have := layout.list_le layout.capacity (by omega); omega
theorem prepend_bounded : (prepend layout).BoundedBy
    (600 * layout.width + 200 + loopTime layout) (2000 * layout.width + 1000 + loopWords layout) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (inputAnswer_bounded layout) (trimmed_bounded layout)).mono
  all_goals have := layout.resetInput_le; have := layout.entry_le; have := layout.list_le layout.capacity (by omega); omega
theorem resetList_bounded : (resetList layout).BoundedBy
    (608 * layout.width + 205 + loopTime layout + ListReverse.timeBudget layout.reverse)
    (2026 * layout.width + 1040 + loopWords layout + ListReverse.codeBudget layout.reverse) := by
  apply (((prepend_bounded layout).then (ListData.cons_boundedBy _ _ _ _ _)).then
    (ListReverse.bounded layout.reverse)).castFunction _ |>.mono
  all_goals
    have := layout.list_le (layout.capacity + 1) (by omega)
    rw [Layouts.list_words] at this
    omega
theorem duplicate_bounded : (duplicate layout).BoundedBy (16 * layout.width) (52 * layout.width + 14) := by
  have size := layout.list_le (layout.capacity + 1) (by omega)
  constructor
  · intro value
    have bound := Assembly.code_time_unit_le
      (Assembly.reads (w := w) 0 0 (layout.list (layout.capacity + 1) (by omega)).representation.encoding.words ++
        Assembly.reads 0 0 (layout.list (layout.capacity + 1) (by omega)).representation.encoding.words)
    simp only [List.length_append, Assembly.reads_length] at bound
    exact bound.trans (by omega)
  · have bound := Assembly.code_descriptionWords_le
      (Assembly.reads (w := w) 0 0 (layout.list (layout.capacity + 1) (by omega)).representation.encoding.words ++
        Assembly.reads 0 0 (layout.list (layout.capacity + 1) (by omega)).representation.encoding.words)
    simp only [List.length_append, Assembly.reads_length] at bound
    exact bound.trans (by omega)

def timeBudget : Nat := 700 * layout.width + 300 + loopTime layout + ListReverse.timeBudget layout.reverse
def codeBudget : Nat := 2200 * layout.width + 1100 + loopWords layout + ListReverse.codeBudget layout.reverse
theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  apply ((resetList_bounded layout).then (duplicate_bounded layout)).mono
  all_goals dsimp only [timeBudget, codeBudget]; omega

variable (slots : Nat)
theorem inputList_names : NamesAccounted (inputList layout).program.code slots :=
  (Implementation.second_names _ _ _ _ slots).seq (Implementation.second_names _ _ _ _ slots)
theorem inputAnswer_names : NamesAccounted (inputAnswer layout).program.code slots :=
  (Implementation.second_names _ _ _ _ slots).seq (Implementation.first_names _ _ _ _ slots)
theorem initialState_names : NamesAccounted (initialState layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (Implementation.first_names _ _ _ _ slots)
    (Implementation.constant_names _ _ _ _ slots)
theorem prepare_names : NamesAccounted (prepare layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (inputList_names layout slots) (initialState_names layout slots)
theorem trimmed_names : NamesAccounted (trimmed layout).program.code slots :=
  ((prepare_names layout slots).seq (loop_names layout slots)).seq (Implementation.second_names _ _ _ _ slots)
theorem prepend_names : NamesAccounted (prepend layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (inputAnswer_names layout slots) (trimmed_names layout slots)
theorem resetList_names : NamesAccounted (resetList layout).program.code slots :=
  ((prepend_names layout slots).seq (ListData.cons_names _ _ _ _ _ slots)).seq (ListReverse.names layout.reverse slots)
theorem duplicate_names : NamesAccounted (duplicate layout).program.code slots :=
  Assembly.code_namesAccounted _ slots ((Assembly.sourcesBound_append _ _ _).mpr
    ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)
theorem names : NamesAccounted (implementation layout).program.code slots :=
  (resetList_names layout slots).seq (duplicate_names layout slots)

omit slots in
theorem resources (tape : RandomTape w) (input : layout.resetInput.Value) (before : State w)
    (holds : layout.resetInput.representation.Holds input before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time input) net peak ∧
      layout.replay.representation.Holds
        ⟨Schnorr.LazySeed.State.fromTape (Schnorr.SeedTape.reset 1 input.val.1 input.val.2.1 input.val.2.2),
          (implementation layout).preserves input.val input.property⟩ after ∧
      (implementation layout).program.time input ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
            5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, memory⟩ :=
    (bounded layout).memoryBound (names layout 0) tape input before holds registers buffers initialRegisters initialBuffers
  exact ⟨after, net, peak, execution, output, elapsed, fun between visited => by
    simpa using (memory between visited).2.2.2⟩

omit slots in
/-- Executing the reset on the fork's challenge packet computes the existing
raw-tape restart, with the same full resource bound. Preparing this input packet
is a separate, charged part of the caller/fork composition. -/
theorem restart_resources [Zero F] (slot : Nat) (answer : F) (state : Schnorr.RawTape.State F)
    (valid : layout.resetInput.valid (slot, (1, answer, 0), state.saved))
    (tape : RandomTape w) (before : State w)
    (holds : layout.resetInput.representation.Holds ⟨(slot, (1, answer, 0), state.saved), valid⟩ before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time ⟨(slot, (1, answer, 0), state.saved), valid⟩) net peak ∧
      layout.replay.representation.Holds
        ⟨Schnorr.RawTape.restart slot answer state, (implementation layout).preserves _ valid⟩ after ∧
      (implementation layout).program.time ⟨(slot, (1, answer, 0), state.saved), valid⟩ ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
            5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout :=
  resources layout tape ⟨(slot, (1, answer, 0), state.saved), valid⟩ before holds registers buffers initialRegisters initialBuffers

end Signatures.Runtime.CaliperBackend.SchnorrROMTape
