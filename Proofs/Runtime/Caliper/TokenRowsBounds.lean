import Proofs.Runtime.Caliper.TokenRows

/-! Derived whole-program bounds for chronological coefficient matching. The
complete stored coefficient list is represented and copied even when its suffix
does not correspond to any transcript token. -/

namespace Signatures.Runtime.CaliperBackend.TokenRows
open Caliper BoundedSource
variable {w : Nat} {K V : Type} (layout : AttachRows.Layouts w K V)

theorem keys_bounded : (keys layout).BoundedBy
    (8 * layout.width + ListReverse.timeBudget (reversal layout))
    (26 * layout.width + 15 + ListReverse.codeBudget (reversal layout)) := by
  apply ((Implementation.first_boundedBy layout.keys layout.values layout.wordFits _).then (ListReverse.bounded (reversal layout))).mono
  all_goals have := layout.base_sizes; omega
theorem values_bounded : (values layout).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.second_boundedBy _ _ _ _).mono
  all_goals have := layout.base_sizes; omega

variable (default : layout.value.Value)
theorem constant_bounded : (constant layout default).BoundedBy (8 * layout.width) (26 * layout.width + 14) := by
  apply (Implementation.constant_bounded _ _ _ _).mono
  all_goals have := layout.base_sizes; omega
theorem environment_bounded : (environment layout default).BoundedBy (172 * layout.width) (559 * layout.width + 152) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (constant_bounded layout default) (values_bounded layout)).mono
  all_goals have := input_size layout; have := layout.base_sizes; omega
theorem prepare_bounded : (prepare layout default).BoundedBy
    (336 * layout.width + ListReverse.timeBudget (reversal layout))
    (1092 * layout.width + 291 + ListReverse.codeBudget (reversal layout)) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (keys_bounded layout) (environment_bounded layout default)).mono
  all_goals have := input_size layout; have := layout.base_sizes; omega
def timeBudget : Nat := 336 * layout.width + ListReverse.timeBudget (reversal layout) + AttachRows.timeBudget layout
def codeBudget : Nat := 1092 * layout.width + 292 + ListReverse.codeBudget (reversal layout) + AttachRows.codeBudget layout
theorem bounded : (implementation layout default).BoundedBy (timeBudget layout) (codeBudget layout) := by
  exact ((prepare_bounded layout default).then (AttachRows.bounded layout)).mono (by rfl) (by unfold codeBudget; omega)

theorem keys_names (slots : Nat) : NamesAccounted (keys layout).program.code slots :=
  (Implementation.first_names _ _ _ _ slots).seq (ListReverse.names _ slots)
theorem values_names (slots : Nat) : NamesAccounted (values layout).program.code slots := Implementation.second_names _ _ _ _ slots
theorem constant_names (slots : Nat) : NamesAccounted (constant layout default).program.code slots := Implementation.constant_names _ _ _ _ slots
theorem environment_names (slots : Nat) : NamesAccounted (environment layout default).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (constant_names layout default slots) (values_names layout slots)
theorem prepare_names (slots : Nat) : NamesAccounted (prepare layout default).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _ (keys_names layout slots) (environment_names layout default slots)
theorem names (slots : Nat) : NamesAccounted (implementation layout default).program.code slots :=
  (prepare_names layout default slots).seq (AttachRows.names layout slots)
theorem static_bound (registers buffers : Nat) :
    staticWords (implementation layout default).program.code registers buffers ≤ 5 * codeBudget layout + registers + 3 * buffers := by
  have stored := (bounded layout default).code_le
  have registersBound := (names layout default 0).registers
  have buffersBound := (names layout default 0).buffers
  unfold staticWords
  omega
theorem resources (tape : RandomTape w) (value : (input layout).Value) (before : State w)
    (holds : (input layout).representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout default).program.code before after
      ((implementation layout default).program.time value) net peak ∧
      layout.output.representation.Holds
        ⟨value.val.1.reverse.mapIdx (fun n key => (key, (value.val.2[n]?).getD default.val)),
          (implementation layout default).preserves value.val value.property⟩ after ∧
      (implementation layout default).program.time value ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout default).program.code before between ∨ between = after) →
        (staticWords (implementation layout default).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout default).program.code.memBound) ≤
          5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, _, _⟩ := (bounded layout default).exec (by decide) tape value before holds
  refine ⟨after, net, peak, execution, output, elapsed, ?_⟩
  intro between visited
  have memory := (LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1).2.2.2
  have stored := static_bound layout default registers buffers
  omega

end Signatures.Runtime.CaliperBackend.TokenRows
