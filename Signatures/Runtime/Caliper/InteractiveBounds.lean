import Signatures.Runtime.Caliper.InteractiveRetain

/-! Uniform bounds on actual interactive execution. Primitive time assumptions
refer to certified Caliper realizers, independently of the old source cost table.
Refinement supplies the represented intermediate states used in composition.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper OracleComp OracleSpec

variable {w : Nat}

theorem WordIO.Exec.net_le_time {cost : WordIO.Costs} {tape : RandomTape w}
    {code : WordIO.Code w} {before after : State w} {trace : List (WordIO.Event w)}
    {time : Nat} {net peak : Int} (execution : WordIO.Exec cost tape code before after trace time net peak)
    (allocation : 1 ≤ cost.machine.allocPerWord) : net ≤ time := by
  induction execution with
  | compute execution => exact execution.net_le_time allocation
  | read | write | invoke => positivity
  | seq _ _ ih₁ ih₂ => push_cast; omega
  | branch_yes _ _ ih | branch_no _ _ ih => push_cast; omega

theorem WordIO.Exec.peak_le_time {cost : WordIO.Costs} {tape : RandomTape w}
    {code : WordIO.Code w} {before after : State w} {trace : List (WordIO.Event w)}
    {time : Nat} {net peak : Int} (execution : WordIO.Exec cost tape code before after trace time net peak)
    (allocation : 1 ≤ cost.machine.allocPerWord) : peak ≤ time := by
  induction execution with
  | compute execution => exact execution.peak_le_time allocation
  | read | write | invoke => positivity
  | seq left _ ih₁ ih₂ =>
    have := left.net_le_time allocation
    push_cast
    omega
  | branch_yes _ _ ih | branch_no _ _ ih => push_cast; omega

namespace Interactive

variable {I A B : Type} {spec : OracleSpec I}
    {port : Port w spec} {cost : WordIO.Costs}

def TimeBound (port : Port w spec) (cost : WordIO.Costs)
    (input : Representation w A) (code : Code w) (budget : Nat) : Prop :=
  ∀ tape value before, input.Holds value before →
    ∀ finished, some finished ∈ support (code.execute port cost tape before) → finished.time ≤ budget

theorem TimeBound.mono {input : Representation w A} {code : Code w} {budget larger : Nat}
    (bounded : TimeBound port cost input code budget) (increase : budget ≤ larger) :
    TimeBound port cost input code larger := by
  intro tape value before holds finished reached
  exact (bounded tape value before holds finished reached).trans increase

theorem TimeBound.viewInput {input : Representation w A} {code : Code w} {budget : Nat}
    (bounded : TimeBound port cost input code budget) (newInput : Representation w B) (view : B → A)
    (sameBytes : ∀ value, input.encoding.encode (view value) = newInput.encoding.encode value) :
    TimeBound port cost newInput code budget := by
  intro tape value before holds
  exact bounded tape (view value) before
    ⟨holds.1, holds.2.1.trans (sameBytes value).symm, holds.2.2⟩

theorem TimeBound.compute {input : Representation w A} {output : Representation w B} {f : A → B}
    (body : Realizer cost.machine input output f) (budget : Nat) (bounded : ∀ value, body.time value ≤ budget) :
    TimeBound port cost input (.compute body.code) budget := by
  intro tape value before holds finished reached
  obtain ⟨after, net, peak, execution, _, _, _⟩ := body.correct tape value before holds
  rw [execute_of_exec port cost tape execution] at reached
  simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at reached
  subst finished
  exact bounded value

theorem TimeBound.compute_loopFree (input : Representation w A) (code : Stmt w) (loopFree : code.LoopFree) :
    TimeBound port cost input (.compute code) (code.staticTime cost.machine) := by
  intro tape value before _ finished reached
  classical
  simp only [Code.execute, support_pure, Set.mem_singleton_iff] at reached
  unfold Caliper.outcome at reached
  split_ifs at reached with terminates
  · have equal : finished = ofOutcome (Classical.choose terminates) := Option.some.inj reached
    subst finished
    exact (Classical.choose_spec terminates).time_le_staticTime_of_loopFree loopFree
  · simp at reached

theorem TimeBound.query : TimeBound port cost port.request .query
    (WordIO.exchangeTime cost port.request.encoding.words port.reply.encoding.words) := by
  intro tape value before holds finished reached
  rw [Code.execute, port.call_eq cost tape value before holds] at reached
  obtain ⟨answer, reached⟩ := Set.mem_iUnion.mp reached
  obtain ⟨result, execution, _, _, time, _, _, _⟩ :=
    WordIO.exchange_run cost tape port.request port.reply value ⟨value, answer⟩ before holds []
  simp only [List.append_nil] at execution
  change some finished = WordIO.run cost tape 2
    (WordIO.exchange port.request.encoding.words port.reply.encoding.words) before
    (port.reply.encoding.encode ⟨value, answer⟩) at reached
  rw [execution] at reached
  cases Option.some.inj reached
  exact time.le

theorem time_seq_at (tape : RandomTape w) (before : State w) (first second : Code w) (leftBudget rightBudget : Nat)
    (leftBound : ∀ left, some left ∈ support (first.execute port cost tape before) → left.time ≤ leftBudget)
    (rightBound : ∀ left, some left ∈ support (first.execute port cost tape before) →
      ∀ right, some right ∈ support (second.execute port cost tape left.state) → right.time ≤ rightBudget) :
    ∀ finished, some finished ∈ support ((Code.seq first second).execute port cost tape before) →
      finished.time ≤ leftBudget + rightBudget := by
  intro finished reached
  simp only [Code.execute, mem_support_bind_iff] at reached
  obtain ⟨left, leftReached, reached⟩ := reached
  cases left with
  | none => simp at reached
  | some left =>
    change some finished ∈ support ((fun right => join left <$> right) <$>
      second.execute port cost tape left.state) at reached
    rw [support_map, Set.mem_image] at reached
    obtain ⟨right, rightReached, equal⟩ := reached
    cases right with
    | none => simp at equal
    | some right =>
      have equal : join left right = finished := Option.some.inj equal
      subst finished
      exact Nat.add_le_add (leftBound left leftReached) (rightBound left leftReached right rightReached)

theorem TimeBound.seq {input : Representation w A} {middle : Representation w B}
    {source : A → OracleComp spec B} {first second : Code w} {leftBudget rightBudget : Nat}
    (firstRefines : Refines port cost input middle source first)
    (leftBound : TimeBound port cost input first leftBudget)
    (rightBound : TimeBound port cost middle second rightBudget) :
    TimeBound port cost input (.seq first second) (leftBudget + rightBudget) := by
  intro tape value before holds
  apply time_seq_at tape before first second leftBudget rightBudget (leftBound tape value before holds)
  intro left reached
  obtain ⟨value, _, result, equal, represented, _, _⟩ := (firstRefines tape value before holds).right_support reached
  cases Option.some.inj equal
  exact rightBound tape value left.state represented

/-- A uniform time bound also bounds additional buffer capacity. Initial stored
data, code, register slots and descriptors require their separate static account. -/
theorem TimeBound.bufferPeak {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {code : Code w} {budget : Nat}
    (refines : Refines port cost input output source code) (bounded : TimeBound port cost input code budget)
    (allocation : 1 ≤ cost.machine.allocPerWord) (tape : RandomTape w) (value : A) (before : State w)
    (holds : input.Holds value before) (finished : WordIO.Result w)
    (reached : some finished ∈ support (code.execute port cost tape before)) : finished.peak ≤ budget := by
  have time := bounded tape value before holds finished reached
  obtain ⟨value, _, result, equal, _, _, execution⟩ := (refines tape value before holds).right_support reached
  cases Option.some.inj equal
  exact (execution.peak_le_time allocation).trans (by exact_mod_cast time)

end Interactive
end Signatures.Runtime.CaliperBackend
