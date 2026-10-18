import Signatures.Runtime.Caliper.WordResources

/-! Frame and well-formedness invariants at every visited instruction boundary,
including inside local Caliper blocks. Thus finite slot reservations cover all
live registers and buffers, not merely a truncated sum of the final state's data.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

namespace LocalReach

variable {cost : CostModel} {tape : RandomTape w} {code : Stmt w} {before between : State w}

theorem frame_reg (reached : Caliper.Reaches cost tape code before between) {register : Reg}
    (untouched : ¬ code.Writes register) : between.regs register = before.regs register := by
  induction reached with
  | start => rfl
  | seq_left _ ih | ifNZ_true _ _ ih | while_guard _ ih => exact ih (fun h => untouched (.inl h))
  | ifNZ_false _ _ ih => exact ih (fun h => untouched (.inr h))
  | seq_right first _ ih | while_body first _ _ ih =>
    exact (ih (fun h => untouched (.inr h))).trans (first.frame_reg (fun h => untouched (.inl h)))
  | while_loop guard _ body _ ih =>
    exact (ih untouched).trans ((body.frame_reg (fun h => untouched (.inr h))).trans
      (guard.frame_reg (fun h => untouched (.inl h))))

theorem frame_cap (reached : Caliper.Reaches cost tape code before between) {buffer : BufId}
    (untouched : ¬ code.Touches buffer) : between.caps buffer = before.caps buffer := by
  induction reached with
  | start => rfl
  | seq_left _ ih | ifNZ_true _ _ ih | while_guard _ ih => exact ih (fun h => untouched (.inl h))
  | ifNZ_false _ _ ih => exact ih (fun h => untouched (.inr h))
  | seq_right first _ ih | while_body first _ _ ih =>
    exact (ih (fun h => untouched (.inr h))).trans (first.frame_cap (fun h => untouched (.inl h)))
  | while_loop guard _ body _ ih =>
    exact (ih untouched).trans ((body.frame_cap (fun h => untouched (.inr h))).trans
      (guard.frame_cap (fun h => untouched (.inl h))))

theorem wellFormed (reached : Caliper.Reaches cost tape code before between) (initial : before.WellFormed) :
    between.WellFormed := by
  induction reached with
  | start => exact initial
  | seq_left _ ih | ifNZ_true _ _ ih | ifNZ_false _ _ ih | while_guard _ ih => exact ih initial
  | seq_right first _ ih | while_body first _ _ ih => exact ih (first.wellFormed_preserved initial)
  | while_loop guard _ body _ ih => exact ih (body.wellFormed_preserved (guard.wellFormed_preserved initial))

end LocalReach

namespace WordIO

variable {cost : Costs} {tape : RandomTape w} {code : Code w}
    {before after between : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
    {execution : Exec cost tape code before after trace time net peak}

theorem Exec.Visits.frame_reg (reached : execution.Visits between) {register : Reg}
    (untouched : ¬ code.Writes register) : between.regs register = before.regs register := by
  induction reached with
  | start => rfl
  | finish execution => exact execution.frame_reg untouched
  | compute _ reached => exact LocalReach.frame_reg reached untouched
  | seq_left _ _ _ ih | branch_yes _ _ _ ih => exact ih (fun h => untouched (.inl h))
  | branch_no _ _ _ ih => exact ih (fun h => untouched (.inr h))
  | seq_right first _ _ ih =>
    exact (ih (fun h => untouched (.inr h))).trans (first.frame_reg (fun h => untouched (.inl h)))

theorem Exec.Visits.frame_cap (reached : execution.Visits between) {buffer : BufId}
    (untouched : ¬ code.Touches buffer) : between.caps buffer = before.caps buffer := by
  induction reached with
  | start => rfl
  | finish execution => exact (execution.frame_buf untouched).2
  | compute _ reached => exact LocalReach.frame_cap reached untouched
  | seq_left _ _ _ ih | branch_yes _ _ _ ih => exact ih (fun h => untouched (.inl h))
  | branch_no _ _ _ ih => exact ih (fun h => untouched (.inr h))
  | seq_right first _ _ ih =>
    exact (ih (fun h => untouched (.inr h))).trans (first.frame_buf (fun h => untouched (.inl h))).2

theorem Exec.Visits.wellFormed (reached : execution.Visits between) (initial : before.WellFormed) :
    between.WellFormed := by
  induction reached with
  | start => exact initial
  | finish execution => exact execution.wellFormed_preserved initial
  | compute _ reached => exact LocalReach.wellFormed reached initial
  | seq_left _ _ _ ih | branch_yes _ _ _ ih | branch_no _ _ _ ih => exact ih initial
  | seq_right first _ _ ih => exact ih (first.wellFormed_preserved initial)

theorem Exec.Visits.registerBound (reached : execution.Visits between) {registers : Nat}
    (initial : RegisterBound before registers) : RegisterBound between (max registers code.registerSlots) := by
  intro register outside
  rw [reached.frame_reg (fun h => Nat.not_lt_of_ge ((le_max_right _ _).trans outside)
    (Code.writes_lt_registerSlots h))]
  exact initial register ((le_max_left _ _).trans outside)

theorem Exec.Visits.supportBound (reached : execution.Visits between) {buffers : Nat}
    (initial : before.SupportBound buffers) : between.SupportBound (max buffers code.memBound) := by
  intro buffer outside
  rw [reached.frame_cap (fun h => Nat.not_lt_of_ge ((le_max_right _ _).trans outside)
    (Code.touches_lt_memBound h))]
  exact initial buffer ((le_max_left _ _).trans outside)

/-- Every counted state has all data inside the reserved slots and satisfies the
capacity invariant, so the live-capacity sum covers every allocated buffer. -/
theorem Exec.Visits.total_memory_bound (reached : execution.Visits between)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers)
    (initialBuffers : before.SupportBound buffers) (initialWellFormed : before.WellFormed) :
    RegisterBound between (max registers code.registerSlots) ∧
    between.SupportBound (max buffers code.memBound) ∧ between.WellFormed ∧
    (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
      code.staticWords registers buffers + before.liveMem (max buffers code.memBound) + peak :=
  ⟨reached.registerBound initialRegisters, reached.supportBound initialBuffers,
    reached.wellFormed initialWellFormed, reached.memory_bound registers buffers⟩

end WordIO
end Signatures.Runtime.CaliperBackend
