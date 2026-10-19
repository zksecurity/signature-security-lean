import Signatures.Runtime.Caliper.ListIndex

/-! Uniform resources of the complete index program. The bounds include the
stored unrolled scan, all preparation and projection copies, and every visited
machine state. They depend on stored capacity, not the source value domain. -/

namespace Signatures.Runtime.CaliperBackend.ListIndex
open Caliper BoundedSource
variable {w : Nat} {V : Type} (layout : Layouts w V)

theorem inputIndex_bounded : (inputIndex layout).BoundedBy 8 40 := Implementation.first_boundedBy _ _ _ _
theorem inputTail_bounded : (inputTail layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.second_boundedBy _ _ _ _).mono
  all_goals have := layout.sizes; omega
theorem inputDefault_bounded : (inputDefault layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((inputTail_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).mono
  all_goals have := layout.value_le; omega
theorem inputList_bounded : (inputList layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((inputTail_bounded layout).then (Implementation.second_boundedBy _ _ _ _)).mono
  all_goals have := layout.sizes; omega
theorem initialFlag_bounded : (initialFlag layout).BoundedBy 8 40 := Implementation.constant_bounded _ _ _ _
theorem initialUnit_bounded : (initialUnit layout).BoundedBy 0 14 := Implementation.constant_bounded _ _ _ _
theorem initialPayload_bounded : (initialPayload layout).BoundedBy (84 * layout.width + 44) (273 * layout.width + 310) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (initialFlag_bounded layout) (inputDefault_bounded layout)).mono
  all_goals simp only [Layouts.boolean_words]; have := layout.sizes; have := layout.value_le; omega
theorem initialState_bounded : (initialState layout).BoundedBy (152 * layout.width + 88) (494 * layout.width + 591) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (inputIndex_bounded layout) (initialPayload_bounded layout)).mono
  all_goals simp only [Layouts.counter_words]; have := layout.sizes; omega
theorem initialTail_bounded : (initialTail layout).BoundedBy (240 * layout.width + 88) (780 * layout.width + 729) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (initialState_bounded layout) (initialUnit_bounded layout)).mono
  all_goals simp only [Layouts.unit_words]; have := layout.sizes; omega
theorem prepare_bounded : (prepare layout).BoundedBy (360 * layout.width + 88) (1170 * layout.width + 882) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (inputList_bounded layout) (initialTail_bounded layout)).mono
  all_goals simp only [Layouts.stateTail_words]; have := layout.sizes; omega
theorem result_bounded : (result layout).BoundedBy (16 * layout.width) (52 * layout.width + 29) := by
  apply ((Implementation.second_boundedBy layout.counter layout.payload layout.wordFits layout.state.representation.fits).then
    (Implementation.second_boundedBy layout.boolean layout.value layout.wordFits layout.payload.representation.fits)).mono
  all_goals have := layout.sizes; have := layout.value_le; omega

theorem fold_width : ListFold.width layout.value.representation.encoding.words layout.state.representation.encoding.words
    layout.unit.representation.encoding.words layout.capacity ≤ 2 * layout.width := by
  simp only [ListFold.width, Layouts.state_words, Layouts.unit_words]
  dsimp only [Layouts.width]
  nlinarith
theorem loop_bounded : (loop layout).BoundedBy
    (8 * layout.width + layout.capacity * (1088 * layout.width + 407))
    (26 * layout.width + 14 + layout.capacity * (3638 * layout.width + 2615)) := by
  apply (FoldImplementation.compile_boundedBy layout.value layout.state layout.unit layout.argFits (body layout)
    layout.wordFits _ layout.capacity layout.countFits layout.frameFits _ _ (body_bounded layout)).mono
  · have step := Nat.mul_le_mul_left layout.capacity (show 1000 * layout.width + 400 + 44 *
        ListFold.width layout.value.representation.encoding.words layout.state.representation.encoding.words
          layout.unit.representation.encoding.words layout.capacity + 7 ≤ 1088 * layout.width + 407 by
        have := fold_width layout; omega)
    have := layout.sizes; omega
  · have step := Nat.mul_le_mul_left layout.capacity (show 3300 * layout.width + 2500 + 169 *
        ListFold.width layout.value.representation.encoding.words layout.state.representation.encoding.words
          layout.unit.representation.encoding.words layout.capacity + 115 ≤ 3638 * layout.width + 2615 by
        have := fold_width layout; omega)
    have := layout.sizes; omega

def timeBudget : Nat := 384 * layout.width + 88 + layout.capacity * (1088 * layout.width + 407)
def codeBudget : Nat := 1248 * layout.width + 927 + layout.capacity * (3638 * layout.width + 2615)
theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  have combined := ((prepare_bounded layout).then (loop_bounded layout)).then (result_bounded layout)
  constructor
  · intro value
    exact (combined.time_le value).trans (by unfold timeBudget; omega)
  · exact combined.code_le.trans (by unfold codeBudget; omega)

theorem inputIndex_names (slots : Nat) : NamesAccounted (inputIndex layout).program.code slots := Implementation.first_names _ _ _ _ slots
theorem inputTail_names (slots : Nat) : NamesAccounted (inputTail layout).program.code slots := Implementation.second_names _ _ _ _ slots
theorem inputDefault_names (slots : Nat) : NamesAccounted (inputDefault layout).program.code slots :=
  (inputTail_names layout slots).seq (Implementation.first_names _ _ _ _ slots)
theorem inputList_names (slots : Nat) : NamesAccounted (inputList layout).program.code slots :=
  (inputTail_names layout slots).seq (Implementation.second_names _ _ _ _ slots)
theorem initialFlag_names (slots : Nat) : NamesAccounted (initialFlag layout).program.code slots := Implementation.constant_names _ _ _ _ slots
theorem initialUnit_names (slots : Nat) : NamesAccounted (initialUnit layout).program.code slots := Implementation.constant_names _ _ _ _ slots
theorem initialPayload_names (slots : Nat) : NamesAccounted (initialPayload layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (initialFlag_names layout slots) (inputDefault_names layout slots)
theorem initialState_names (slots : Nat) : NamesAccounted (initialState layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (inputIndex_names layout slots) (initialPayload_names layout slots)
theorem initialTail_names (slots : Nat) : NamesAccounted (initialTail layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (initialState_names layout slots) (initialUnit_names layout slots)
theorem prepare_names (slots : Nat) : NamesAccounted (prepare layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (inputList_names layout slots) (initialTail_names layout slots)
theorem loop_names (slots : Nat) : NamesAccounted (loop layout).program.code slots :=
  FoldImplementation.compile_names _ _ _ _ _ _ _ _ _ _ (body_names layout slots)
theorem result_names (slots : Nat) : NamesAccounted (result layout).program.code slots :=
  (Implementation.second_names _ _ _ _ slots).seq (Implementation.second_names _ _ _ _ slots)
theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots :=
  ((prepare_names layout slots).seq (loop_names layout slots)).seq (result_names layout slots)

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
      layout.value.representation.Holds
        ⟨(value.val.2.2[value.val.1]?).getD value.val.2.1, (implementation layout).preserves value.val value.property⟩ after ∧
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

end Signatures.Runtime.CaliperBackend.ListIndex
