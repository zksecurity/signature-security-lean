import Signatures.Runtime.Caliper.InteractiveBounds

/-! Executed control overhead, uniform over represented inputs and oracle replies.
Bounded loops charge every executed payload copy; saved-state wrappers charge
preparation and reconstruction around the interactive callee.
-/

namespace Signatures.Runtime.CaliperBackend.Interactive

open Caliper OracleComp OracleSpec

variable {w : Nat} {I A B D S : Type} {spec : OracleSpec I}
    {port : Port w spec} {cost : WordIO.Costs}

theorem time_prepend_at (tape : RandomTape w)
    {prefixCode : Stmt w} {body : Code w} {before middle : State w}
    {time budget : Nat} {net peak : Int}
    (execution : Caliper.Exec cost.machine tape prefixCode before middle time net peak)
    (bounded : ∀ finished, some finished ∈ support (body.execute port cost tape middle) → finished.time ≤ budget) :
    ∀ finished, some finished ∈ support ((Code.seq (.compute prefixCode) body).execute port cost tape before) →
      finished.time ≤ time + budget := by
  intro finished reached
  rw [Code.execute, execute_of_exec port cost tape execution] at reached
  simp only [pure_bind] at reached
  change some finished ∈ support ((fun right => join ⟨middle, time, net, peak, [], []⟩ <$> right) <$>
    body.execute port cost tape middle) at reached
  rw [support_map, Set.mem_image] at reached
  obtain ⟨right, rightReached, equal⟩ := reached
  cases right with
  | none => simp at equal
  | some right =>
    have equal : join ⟨middle, time, net, peak, [], []⟩ right = finished := Option.some.inj equal
    subst finished
    exact Nat.add_le_add_left (bounded right rightReached) time

theorem time_branch_at (tape : RandomTape w) (before : State w) (condition : Reg) (yes no : Code w) (budget : Nat)
    (bounded : ∀ finished, some finished ∈ support
      ((if before.regs condition = 0 then no else yes).execute port cost tape before) → finished.time ≤ budget) :
    ∀ finished, some finished ∈ support ((Code.branch condition yes no).execute port cost tape before) →
      finished.time ≤ cost.machine.branch + budget := by
  intro finished reached
  have choice : (if before.regs condition = 0 then no.execute port cost tape before else yes.execute port cost tape before) =
      (if before.regs condition = 0 then no else yes).execute port cost tape before := by split_ifs <;> rfl
  rw [Code.execute, choice, support_map, Set.mem_image] at reached
  obtain ⟨result, reached, equal⟩ := reached
  cases result with
  | none => simp at equal
  | some result =>
    have equal : { result with time := cost.machine.branch + result.time } = finished := Option.some.inj equal
    subst finished
    exact Nat.add_le_add_left (bounded result reached) cost.machine.branch

theorem time_payload_at (tape : RandomTape w)
    {input : Representation w A} {body : Code w} {budget : Nat}
    (bounded : TimeBound port cost input body budget)
    (value : A) (tag : Word w) (padding : List (Word w)) (before : State w)
    (zero : before.regs 0 = 0)
    (contents : (before.bufs 0).toList = tag :: (input.encoding.encode value ++ padding))
    (wellFormed : before.WellFormed) (capacities : ∀ buffer, before.caps buffer < 2 ^ w) :
    ∀ finished, some finished ∈ support
      ((Code.seq (.compute (selectSlice 1 input.encoding.words)) body).execute port cost tape before) →
      finished.time ≤ (selectSlice (w := w) 1 input.encoding.words).staticTime cost.machine + budget := by
  have length := congrArg List.length contents
  have span : 1 + input.encoding.words ≤ (before.bufs 0).size := by
    simp only [Array.length_toList, List.length_cons, List.length_append, input.encoding.encode_length] at length
    omega
  obtain ⟨middle, time, net, peak, execution, payload, offset, caps⟩ :=
    selectSlice_exec cost.machine tape 1 input.encoding.words before span capacities wellFormed
  have timeEq := execution.straight_time_eq (selectSlice_straight _ _)
  rw [← timeEq]
  apply time_prepend_at tape execution
  apply bounded tape value middle
  refine ⟨offset.trans zero, ?_, execution.wellFormed_preserved wellFormed, caps⟩
  rw [payload, contents, ← input.encoding.encode_length value]
  simp

def dispatchTime (cost : WordIO.Costs) (leftWords rightWords leftBudget rightBudget : Nat) : Nat :=
  cost.machine.memLoad + (cost.machine.branch +
    max ((selectSlice (w := w) 1 leftWords).staticTime cost.machine + leftBudget)
      ((selectSlice (w := w) 1 rightWords).staticTime cost.machine + rightBudget))

theorem TimeBound.dispatch (left : Representation w A) (right : Representation w B)
    {leftBody rightBody : Code w} {leftBudget rightBudget : Nat}
    (leftBound : TimeBound port cost left leftBody leftBudget)
    (rightBound : TimeBound port cost right rightBody rightBudget)
    (hw : 0 < w) (fits : 1 + max left.encoding.words right.encoding.words < 2 ^ w) :
    TimeBound port cost (left.sum right hw fits)
      (dispatch leftBody rightBody left.encoding.words right.encoding.words)
      (dispatchTime (w := w) cost left.encoding.words right.encoding.words leftBudget rightBudget) := by
  intro tape value before represented
  cases value with
  | inl value =>
    have contents : (before.bufs 0).toList = (0 : Word w) :: (left.encoding.encode value ++
        List.replicate (max left.encoding.words right.encoding.words - left.encoding.words) 0) := represented.2.1
    have loaded := Dispatch.load_tag cost.machine tape 0 _ before represented.1 contents
    apply time_prepend_at tape loaded
    apply time_branch_at
    simp only [regs_setReg_self, ite_true]
    intro finished reached
    exact (time_payload_at tape leftBound value 0 _ (before.setReg 1 0)
      (by simpa using represented.1) contents (loaded.wellFormed_preserved represented.2.2.1)
      represented.2.2.2 finished reached).trans (le_max_left _ _)
  | inr value =>
    have contents : (before.bufs 0).toList = (1 : Word w) :: (right.encoding.encode value ++
        List.replicate (max left.encoding.words right.encoding.words - right.encoding.words) 0) := represented.2.1
    have loaded := Dispatch.load_tag cost.machine tape 1 _ before represented.1 contents
    apply time_prepend_at tape loaded
    apply time_branch_at
    have nonzero : (before.setReg 1 1).regs 1 ≠ 0 := by simp [hw.ne']
    rw [ite_eq_right nonzero]
    intro finished reached
    exact (time_payload_at tape rightBound value 1 _ (before.setReg 1 1)
      (by simpa using represented.1) contents (loaded.wellFormed_preserved represented.2.2.1)
      represented.2.2.2 finished reached).trans (le_max_right _ _)

theorem TimeBound.retain {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {body : Code w} {budget : Nat}
    (bodyRefines : Refines port cost input output source body)
    (bounded : TimeBound port cost input body budget)
    (allocation : 1 ≤ cost.machine.allocPerWord) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (inputFits : input.encoding.words + saved.encoding.words < 2 ^ w) :
    TimeBound port cost (input.prod saved inputFits)
      (retain body (savedBuffer port body) input.encoding.words output.encoding.words saved.encoding.words)
      ((Retain.prepare (w := w) (savedBuffer port body) input.encoding.words saved.encoding.words).staticTime cost.machine +
        (budget + (Retain.finish (w := w) (savedBuffer port body) output.encoding.words saved.encoding.words).staticTime cost.machine)) := by
  intro tape value before represented
  obtain ⟨prepared, time, net, peak, preparing, argument, _⟩ :=
    Retain.prepare_exec cost.machine allocation tape input saved hw inputFits (savedBuffer port body)
      (le_max_left _ _) value before represented
  have straight : (Retain.prepare (w := w) (savedBuffer port body) input.encoding.words saved.encoding.words).Straight :=
    ⟨Retain.save_straight _ _ _, selectSlice_straight _ _⟩
  rw [← preparing.straight_time_eq straight]
  apply time_prepend_at tape preparing
  have finishBound := TimeBound.compute_loopFree (port := port) (cost := cost) output
    (Retain.finish (savedBuffer port body) output.encoding.words saved.encoding.words)
    (Stmt.Straight.loopFree ⟨Assembly.code_straight _, trivial⟩)
  exact (bounded.seq bodyRefines finishBound) tape value.1 prepared argument

def loopOverhead (cost : WordIO.Costs) (resultWords stateWords : Nat) : Nat :=
  cost.machine.memLoad + cost.machine.branch + max
    ((selectSlice (w := w) 1 resultWords).staticTime cost.machine)
    ((selectSlice (w := w) 1 stateWords).staticTime cost.machine)

theorem TimeBound.loop (state : Representation w A) (result : Representation w B)
    (hw : 0 < w) (fits : 1 + max result.encoding.words state.encoding.words < 2 ^ w)
    {source : A → OracleComp spec (B ⊕ A)} {body stop : Code w} {bodyBudget stopBudget : Nat}
    (bodyRefines : Refines port cost state (result.sum state hw fits) source body)
    (bodyBound : TimeBound port cost state body bodyBudget) (stopBound : TimeBound port cost state stop stopBudget)
    (fuel : Nat) : TimeBound port cost state (loop body stop result.encoding.words state.encoding.words fuel)
      (stopBudget + fuel * (bodyBudget + loopOverhead (w := w) cost result.encoding.words state.encoding.words)) := by
  induction fuel with
  | zero => simpa [Interactive.loop] using stopBound
  | succ fuel ih =>
    have skipBound : TimeBound port cost result (.compute .skip) 0 :=
      TimeBound.compute_loopFree result .skip trivial
    have bounded := bodyBound.seq bodyRefines (skipBound.dispatch result state ih hw fits)
    apply bounded.mono
    simp only [dispatchTime, loopOverhead, Nat.succ_mul]
    omega

theorem dispatchTime_unit (leftWords rightWords leftBudget rightBudget : Nat) :
    dispatchTime (w := w) .unit leftWords rightWords leftBudget rightBudget =
      2 + max (8 * leftWords + leftBudget) (8 * rightWords + rightBudget) := by
  simp [dispatchTime, selectSlice_staticTime, sliceWordTime, WordIO.Costs.unit, CostModel.unit]
  omega

theorem loopOverhead_unit (resultWords stateWords : Nat) :
    loopOverhead (w := w) .unit resultWords stateWords = 2 + 8 * max resultWords stateWords := by
  simp [loopOverhead, selectSlice_staticTime, sliceWordTime, WordIO.Costs.unit, CostModel.unit]
  omega

theorem retain_time_unit_le (buffer inputWords outputWords savedWords budget : Nat) :
    (Retain.prepare (w := w) buffer inputWords savedWords).staticTime .unit +
      (budget + (Retain.finish (w := w) buffer outputWords savedWords).staticTime .unit) ≤
      budget + 8 * inputWords + 8 * outputWords + 12 * savedWords := by
  have bound := Assembly.code_time_unit_le (Retain.restoreOperands (w := w) buffer outputWords savedWords)
  simp only [Retain.restoreOperands, List.length_append, Assembly.reads_length] at bound
  simp only [Retain.prepare, Retain.finish, Retain.save, Retain.restoreOperands, Stmt.staticTime,
    copySlice_staticTime, selectSlice_staticTime, sliceWordTime, CostModel.unit] at *
  omega

end Signatures.Runtime.CaliperBackend.Interactive
