import Signatures.Runtime.Caliper.ListReverse
import Signatures.Runtime.Caliper.ExpressionMemory

/-! Uniform bounds for the constructed reversal, including growing fold states,
early-return padding, stored unrolled bodies and all visited machine memory. -/

namespace Signatures.Runtime.CaliperBackend.ListReverse
open Caliper BoundedSource

variable {w : Nat} {A : Type} (layout : Layouts w A)

theorem Layouts.sizes : layout.entry.representation.encoding.words ≤ layout.width ∧
    layout.list.representation.encoding.words ≤ layout.width ∧
    layout.env.representation.encoding.words = 0 ∧ (saved layout).representation.encoding.words = 1 ∧
    ∀ i, (layout.states i).representation.encoding.words ≤ layout.width := by
  have large := Nat.mul_le_mul_right layout.entry.representation.encoding.words (show 1 ≤ layout.capacity + 1 by omega)
  refine ⟨by dsimp only [Layouts.width]; omega, ?_, rfl, ?_, ?_⟩
  · change 1 + layout.capacity * _ ≤ 1 + (layout.capacity + 1) * _
    nlinarith
  · change (1 + 0 * layout.entry.representation.encoding.words) + 0 = 1
    omega
  · intro i
    have := Nat.mul_le_mul_right layout.entry.representation.encoding.words (show i.val ≤ layout.capacity + 1 by omega)
    change 1 + i.val * _ ≤ 1 + (layout.capacity + 1) * _
    omega

theorem body_bounded (i : Fin layout.capacity) : (body layout i).BoundedBy
    (8 * layout.width + 5) (26 * layout.width + 38) := by
  have size := layout.sizes.2.2.2.2 i.succ
  change 1 + (i.val + 1) * layout.entry.representation.encoding.words ≤ layout.width at size
  constructor
  · intro value
    exact (ListConstruct.consCode_time_unit_le (w := w) layout.entry.representation.encoding.words i.val).trans (by omega)
  · exact (ListConstruct.consCode_descriptionWords_le (w := w) layout.entry.representation.encoding.words i.val).trans (by omega)

theorem stop_bounded (i : Fin (layout.capacity + 1)) : (stop layout i).BoundedBy
    (8 * layout.width) (26 * layout.width + 14) := by
  apply (ListData.widen_boundedBy layout.entry i.val layout.capacity (by omega) layout.wordFits layout.countFits
    layout.list.representation.fits).mono
  all_goals have := layout.sizes.2.1; change 1 + layout.capacity * _ ≤ layout.width at this; omega

theorem loop_bounded : (loop layout).BoundedBy
    (StagedFold.timeBudget layout.width (8 * layout.width + 5) (8 * layout.width) layout.capacity)
    (StagedFold.codeBudget layout.width (26 * layout.width + 38) (26 * layout.width + 14) layout.capacity) :=
  StagedFold.compile_boundedBy layout.entry layout.list layout.env layout.wordFits step
    layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (fun i => some (body layout i)) (stop layout)
    layout.width (8 * layout.width + 5) (26 * layout.width + 38) (8 * layout.width) (26 * layout.width + 14)
    layout.sizes.1 (by rw [layout.sizes.2.2.1]; exact Nat.zero_le _) layout.sizes.2.2.2.2
    (fun i implementation equal => Option.some.inj equal ▸ body_bounded layout i)
    (stop_bounded layout) (loop layout) (Option.eq_some_of_isSome (accepted layout))

theorem prepare_bounded : (prepare layout).BoundedBy (88 * layout.width + 24) (286 * layout.width + 217) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _
    (Implementation.identity_boundedBy layout.list (width_pos layout.wordFits))
    (Implementation.constant_bounded layout.list (saved layout) (empty layout) layout.wordFits)).mono
  all_goals have := layout.sizes; omega

def timeBudget : Nat := 88 * layout.width + 24 +
  StagedFold.timeBudget layout.width (8 * layout.width + 5) (8 * layout.width) layout.capacity
def codeBudget : Nat := 286 * layout.width + 218 +
  StagedFold.codeBudget layout.width (26 * layout.width + 38) (26 * layout.width + 14) layout.capacity

theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  have combined := (prepare_bounded layout).then (loop_bounded layout)
  exact ⟨combined.time_le, combined.code_le.trans (by unfold codeBudget; omega)⟩

theorem prepare_buffers : (prepare layout).program.code.memBound ≤ 3 :=
  Implementation.pair_buffers (firstBuffers := 0) (secondBuffers := 2)
    (Implementation.identity layout.list (width_pos layout.wordFits)) _ _ _ _ _ _ _ (show (0 : Nat) ≤ 0 from le_rfl)
    (Implementation.constant_buffers layout.list (saved layout) (empty layout) layout.wordFits)

theorem buffers : (implementation layout).program.code.memBound ≤ 3 :=
  max_le (prepare_buffers layout) (loop_buffers layout)

theorem loop_names (slots : Nat) : NamesAccounted (loop layout).program.code slots :=
  StagedFold.compile_names layout.entry layout.list layout.env layout.wordFits step
    layout.capacity layout.states layout.countFits layout.argFits layout.frameFits (fun i => some (body layout i)) (stop layout) slots
    (by
      intro i implementation equal
      cases Option.some.inj equal
      exact ListData.cons_names layout.entry i.val layout.wordFits (by have := layout.countFits; omega)
        (layout.states i.succ).representation.fits slots)
    (fun i => ListData.widen_names layout.entry i.val layout.capacity (by omega) layout.wordFits layout.countFits
      layout.list.representation.fits slots)
    (loop layout) (Option.eq_some_of_isSome (accepted layout))

theorem prepare_names (slots : Nat) : NamesAccounted (prepare layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (skip_names slots)
    (Implementation.constant_names layout.list (saved layout) (empty layout) layout.wordFits slots)

theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots :=
  (prepare_names layout slots).seq (loop_names layout slots)

theorem static_bound (registers buffers : Nat) :
    staticWords (implementation layout).program.code registers buffers ≤ 5 * codeBudget layout + registers + 3 * buffers := by
  have stored := (bounded layout).code_le
  have registersBound := (names layout 0).registers
  have buffersBound := (names layout 0).buffers
  unfold staticWords
  omega

theorem resources (tape : RandomTape w) (value : layout.list.Value) (before : State w)
    (holds : layout.list.representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time value) net peak ∧
      layout.list.representation.Holds ⟨value.val.reverse, (implementation layout).preserves value.val value.property⟩ after ∧
      (implementation layout).program.time value ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
          5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, _, peakBound⟩ := (bounded layout).exec (by decide) tape value before holds
  refine ⟨after, net, peak, execution, output, elapsed, ?_⟩
  intro between visited
  have memory := (LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1).2.2.2
  have stored := static_bound layout registers buffers
  omega

end Signatures.Runtime.CaliperBackend.ListReverse
