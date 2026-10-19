import Signatures.Runtime.Caliper.AttachRows

/-! Whole-program resource bounds for positional attachment. Both the stored
fold and final reversal are charged, including padding on short key lists. -/

namespace Signatures.Runtime.CaliperBackend.AttachRows
open Caliper BoundedSource
variable {w : Nat} {K V : Type} (layout : Layouts w K V)

theorem reversal_width : layout.reversal.width ≤ layout.width := by
  change 1 + (layout.capacity + 1) * layout.row.representation.encoding.words ≤ _
  rw [Layouts.row_words]
  dsimp only [Layouts.width]
  omega
theorem output_size : layout.output.representation.encoding.words ≤ layout.width := (layout.stage_sizes (Fin.last _)).1
theorem zero_words : (layout.states 0).representation.encoding.words = 2 := by
  rw [Layouts.states_words]; simp
theorem stopCounter_bounded (i : Fin (layout.capacity + 1)) : (stopCounter layout i).BoundedBy 8 42 := by
  have view : (counterView layout i).BoundedBy 0 1 := ⟨fun _ => le_rfl, le_rfl⟩
  exact (Implementation.first_boundedBy _ _ _ _).then view
theorem stopRows_bounded (i : Fin (layout.capacity + 1)) :
    (stopRows layout i).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy (layout.counter i) (layout.rows i) layout.wordFits _).then
    (ListReverse.stop_bounded layout.reversal i)).mono
  all_goals have := layout.stage_sizes i; have := reversal_width layout; omega
theorem stop_bounded (i : Fin (layout.capacity + 1)) :
    (stop layout i).BoundedBy (84 * layout.width + 44) (273 * layout.width + 312) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (stopCounter_bounded layout i) (stopRows_bounded layout i)).mono
  all_goals simp only [Layouts.counter_words]; have := layout.stage_sizes i; have := output_size layout; omega

def loopTime : Nat := StagedFold.timeBudget layout.width (bodyTime layout) (84 * layout.width + 44) layout.capacity
def loopCode : Nat := StagedFold.codeBudget layout.width (bodyCode layout) (273 * layout.width + 312) layout.capacity
theorem loop_bounded : (loop layout).BoundedBy (loopTime layout) (loopCode layout) :=
  StagedFold.compile_boundedBy layout.key layout.result layout.env layout.wordFits step
    layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (fun i => some (body layout i)) (stop layout)
    layout.width (bodyTime layout) (bodyCode layout) (84 * layout.width + 44) (273 * layout.width + 312)
    layout.base_sizes.1 layout.base_sizes.2.2.2.2.2.1 (fun i => (layout.stage_sizes i).2)
    (fun i _implementation equal => Option.some.inj equal ▸ body_bounded layout i)
    (stop_bounded layout) (loop layout) (Option.eq_some_of_isSome (accepted layout))
theorem initialState_bounded : (initialState layout).BoundedBy 16 66 := by
  apply (Implementation.constant_bounded layout.input (layout.states 0) (initial layout) layout.wordFits).mono
  all_goals rw [zero_words]
theorem inputKeys_bounded : (inputKeys layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.first_boundedBy _ _ _ _).mono
  all_goals have := layout.base_sizes; omega
theorem inputEnv_bounded : (inputEnv layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.second_boundedBy _ _ _ _).mono
  all_goals have := layout.base_sizes; omega
theorem prepareSaved_bounded : (prepareSaved layout).BoundedBy (76 * layout.width + 88) (247 * layout.width + 438) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (initialState_bounded layout) (inputEnv_bounded layout)).mono
  all_goals have := zero_words layout; have := layout.base_sizes; omega
theorem prepare_bounded : (prepare layout).BoundedBy (204 * layout.width + 88) (663 * layout.width + 576) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (inputKeys_bounded layout) (prepareSaved_bounded layout)).mono
  all_goals have := saved_size layout; have := layout.base_sizes; omega
theorem finish_bounded : (finish layout).BoundedBy
    (8 * layout.width + ListReverse.timeBudget layout.reversal)
    (26 * layout.width + 15 + ListReverse.codeBudget layout.reversal) := by
  apply ((Implementation.second_boundedBy (layout.counter (Fin.last layout.capacity)) layout.output layout.wordFits _).then
    (ListReverse.bounded layout.reversal)).mono
  all_goals have := output_size layout; omega
def timeBudget : Nat := 212 * layout.width + 88 + loopTime layout + ListReverse.timeBudget layout.reversal
def codeBudget : Nat := 689 * layout.width + 593 + loopCode layout + ListReverse.codeBudget layout.reversal
theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  have combined := ((prepare_bounded layout).then (loop_bounded layout)).then (finish_bounded layout)
  constructor
  · intro value; exact (combined.time_le value).trans (by unfold timeBudget; omega)
  · exact combined.code_le.trans (by unfold codeBudget; omega)

theorem stopCounter_names (i : Fin (layout.capacity + 1)) (slots : Nat) : NamesAccounted (stopCounter layout i).program.code slots :=
  (Implementation.first_names _ _ _ _ slots).seq (skip_names slots)
theorem stopRows_names (i : Fin (layout.capacity + 1)) (slots : Nat) : NamesAccounted (stopRows layout i).program.code slots :=
  (Implementation.second_names _ _ _ _ slots).seq (ListData.widen_names _ _ _ _ _ _ _ slots)
theorem stop_names (i : Fin (layout.capacity + 1)) (slots : Nat) : NamesAccounted (stop layout i).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (stopCounter_names layout i slots) (stopRows_names layout i slots)
theorem loop_names (slots : Nat) : NamesAccounted (loop layout).program.code slots :=
  StagedFold.compile_names layout.key layout.result layout.env layout.wordFits step
    layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (fun i => some (body layout i)) (stop layout) slots
    (fun i _implementation equal => Option.some.inj equal ▸ body_names layout i slots)
    (fun i => stop_names layout i slots) (loop layout) (Option.eq_some_of_isSome (accepted layout))
theorem initialState_names (slots : Nat) : NamesAccounted (initialState layout).program.code slots := Implementation.constant_names _ _ _ _ slots
theorem inputKeys_names (slots : Nat) : NamesAccounted (inputKeys layout).program.code slots := Implementation.first_names _ _ _ _ slots
theorem inputEnv_names (slots : Nat) : NamesAccounted (inputEnv layout).program.code slots := Implementation.second_names _ _ _ _ slots
theorem prepareSaved_names (slots : Nat) : NamesAccounted (prepareSaved layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (initialState_names layout slots) (inputEnv_names layout slots)
theorem prepare_names (slots : Nat) : NamesAccounted (prepare layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (inputKeys_names layout slots) (prepareSaved_names layout slots)
theorem finish_names (slots : Nat) : NamesAccounted (finish layout).program.code slots :=
  (Implementation.second_names _ _ _ _ slots).seq (ListReverse.names _ slots)
theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots :=
  ((prepare_names layout slots).seq (loop_names layout slots)).seq (finish_names layout slots)
theorem static_bound (registers buffers : Nat) :
    staticWords (implementation layout).program.code registers buffers ≤ 5 * codeBudget layout + registers + 3 * buffers := by
  have stored := (bounded layout).code_le
  have registersBound := (names layout 0).registers
  have buffersBound := (names layout 0).buffers
  unfold staticWords
  omega
theorem resources (tape : RandomTape w) (value : layout.input.Value) (before : State w)
    (holds : layout.input.representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time value) net peak ∧
      layout.output.representation.Holds
        ⟨value.val.1.mapIdx (fun n key => (key, (value.val.2.2[n]?).getD value.val.2.1)),
          (implementation layout).preserves value.val value.property⟩ after ∧
      (implementation layout).program.time value ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
          5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, _, _⟩ := (bounded layout).exec (by decide) tape value before holds
  refine ⟨after, net, peak, execution, output, elapsed, ?_⟩
  intro between visited
  have memory := (LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1).2.2.2
  have stored := static_bound layout registers buffers
  omega

end Signatures.Runtime.CaliperBackend.AttachRows
