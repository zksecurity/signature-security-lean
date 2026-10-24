import Proofs.Runtime.Caliper.InteractiveInvariant
import Proofs.Runtime.Caliper.InteractiveMemory

/-! Time and whole-execution memory bounds on reachable domains. Decreasing
capacity reservations affect the proof domain, not the code or its charges. -/

namespace Signatures.Runtime.CaliperBackend.Interactive

open Caliper OracleComp OracleSpec

variable {w : Nat} {I A B : Type} {spec : OracleSpec I}
    {port : Port w spec} {cost : WordIO.Costs}

def TimeBoundOn (predicate : A → Prop) (port : Port w spec) (cost : WordIO.Costs)
    (input : Representation w A) (code : Code w) (budget : Nat) : Prop :=
  ∀ tape value, predicate value → ∀ before, input.Holds value before →
    ∀ finished, some finished ∈ support (code.execute port cost tape before) → finished.time ≤ budget

theorem TimeBound.on {input : Representation w A} {code : Code w} {budget : Nat}
    (bounded : TimeBound port cost input code budget) (predicate : A → Prop) :
    TimeBoundOn predicate port cost input code budget :=
  fun tape value _ before holds => bounded tape value before holds

theorem TimeBoundOn.restrict {predicate : A → Prop} [DecidablePred predicate]
    {input : Representation w A} {code : Code w} {budget : Nat}
    (bounded : TimeBoundOn predicate port cost input code budget) :
    TimeBound port cost (input.restrict predicate) code budget :=
  fun tape value before holds => bounded tape value.val value.property before holds

theorem TimeBoundOn.mono {predicate : A → Prop} {input : Representation w A}
    {code : Code w} {budget larger : Nat} (bounded : TimeBoundOn predicate port cost input code budget)
    (increase : budget ≤ larger) : TimeBoundOn predicate port cost input code larger :=
  fun tape value valid before holds finished reached =>
    (bounded tape value valid before holds finished reached).trans increase

theorem TimeBoundOn.seq {p : A → Prop} {q : B → Prop}
    {input : Representation w A} {middle : Representation w B}
    {source : A → OracleComp spec B} {first second : Code w} {leftBudget rightBudget : Nat}
    (firstRefines : RefinesOn p port cost input middle source first)
    (leftBound : TimeBoundOn p port cost input first leftBudget)
    (rightBound : TimeBoundOn q port cost middle second rightBudget)
    (preserves : ∀ value, p value → ∀ answer ∈ support (source value), q answer) :
    TimeBoundOn p port cost input (.seq first second) (leftBudget + rightBudget) := by
  intro tape value valid before holds
  apply time_seq_at tape before first second leftBudget rightBudget (leftBound tape value valid before holds)
  intro left reached
  obtain ⟨answer, supported, result, equal, represented, _, _⟩ :=
    (firstRefines tape value valid before holds).right_support reached
  cases Option.some.inj equal
  exact rightBound tape answer (preserves value valid answer supported) left.state represented

theorem TimeBoundOn.dispatch (left : Representation w A) (right : Representation w B)
    {p : A → Prop} {q : B → Prop} {leftBody rightBody : Code w} {leftBudget rightBudget : Nat}
    (leftBound : TimeBoundOn p port cost left leftBody leftBudget)
    (rightBound : TimeBoundOn q port cost right rightBody rightBudget)
    (hw : 0 < w) (fits : 1 + max left.encoding.words right.encoding.words < 2 ^ w) :
    TimeBoundOn (Sum.elim p q) port cost (left.sum right hw fits)
      (dispatch leftBody rightBody left.encoding.words right.encoding.words)
      (dispatchTime (w := w) cost left.encoding.words right.encoding.words leftBudget rightBudget) := by
  classical
  have bounded := TimeBound.dispatch (left.restrict p) (right.restrict q)
    leftBound.restrict rightBound.restrict hw fits
  intro tape value valid before holds
  cases value with
  | inl value => exact bounded tape (.inl ⟨value, valid⟩) before holds
  | inr value => exact bounded tape (.inr ⟨value, valid⟩) before holds

theorem TimeBoundOn.retain {S : Type} {predicate : A → Prop}
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {body : Code w} {budget : Nat}
    (refined : RefinesOn predicate port cost input output source body)
    (bounded : TimeBoundOn predicate port cost input body budget)
    (allocation : 1 ≤ cost.machine.allocPerWord) (saved : Representation w S)
    (hw : 16 < 2 ^ w) (inputFits : input.encoding.words + saved.encoding.words < 2 ^ w) :
    TimeBoundOn (fun value => predicate value.1) port cost (input.prod saved inputFits)
      (Interactive.retain body (savedBuffer port body) input.encoding.words output.encoding.words saved.encoding.words)
      ((Retain.prepare (w := w) (savedBuffer port body) input.encoding.words saved.encoding.words).staticTime cost.machine +
        (budget + (Retain.finish (w := w) (savedBuffer port body) output.encoding.words saved.encoding.words).staticTime cost.machine)) := by
  classical
  intro tape value valid before holds
  exact (TimeBound.retain refined.restrict bounded.restrict allocation saved hw inputFits)
    tape (⟨value.1, valid⟩, value.2) before holds

theorem TimeBoundOn.loop (state : Representation w A) (result : Representation w B)
    (invariant : Nat → A → Prop) (hw : 0 < w)
    (fits : 1 + max result.encoding.words state.encoding.words < 2 ^ w)
    {source : A → OracleComp spec (B ⊕ A)} {body stop : Code w} {bodyBudget stopBudget : Nat}
    (bodyRefines : ∀ remaining, RefinesOn (invariant (remaining + 1)) port cost state (result.sum state hw fits) source body)
    (bodyBound : ∀ remaining, TimeBoundOn (invariant (remaining + 1)) port cost state body bodyBudget)
    (stopBound : TimeBoundOn (invariant 0) port cost state stop stopBudget)
    (preserves : ∀ remaining value, invariant (remaining + 1) value →
      ∀ answer ∈ support (source value), Sum.elim (fun _ => True) (invariant remaining) answer)
    (fuel : Nat) : TimeBoundOn (invariant fuel) port cost state
      (loop body stop result.encoding.words state.encoding.words fuel)
      (stopBudget + fuel * (bodyBudget + loopOverhead (w := w) cost result.encoding.words state.encoding.words)) := by
  induction fuel with
  | zero => simpa [Interactive.loop] using stopBound
  | succ fuel ih =>
    have skipBound : TimeBound port cost result (.compute .skip) 0 :=
      TimeBound.compute_loopFree result .skip trivial
    have bounded := TimeBoundOn.seq (bodyRefines fuel) (bodyBound fuel)
      (TimeBoundOn.dispatch result state (skipBound.on (fun _ => True)) ih hw fits) (preserves fuel)
    apply bounded.mono
    simp only [dispatchTime, loopOverhead, Nat.succ_mul]
    omega

/-- All visited memory, stored instructions and the returned value refer to the
same supported execution. The invariant introduces no uncharged storage. -/
theorem RefinesOn.resources {predicate : A → Prop}
    {input : Representation w A} {output : Representation w B}
    {source : A → OracleComp spec B} {code : Code w} {time words slots : Nat}
    (refined : RefinesOn predicate port .unit input output source code)
    (bounded : TimeBoundOn predicate port .unit input code time)
    (stored : (code.lower port).descriptionWords ≤ words) (names : WordIO.NamesBound (code.lower port) slots)
    (tape : RandomTape w) (value : A) (valid : predicate value) (before : State w) (holds : input.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers)
    (finished : WordIO.Result w) (reached : some finished ∈ support (code.execute port .unit tape before)) :
    finished.time ≤ time ∧ ∃ answer ∈ support (source value), output.Holds answer finished.state ∧
      ∃ execution : WordIO.Exec .unit tape (code.lower port) before finished.state finished.trace finished.time finished.net finished.peak,
        ∀ between, execution.Visits between →
          RegisterBound between (max registers (code.lower port).registerSlots) ∧
          between.SupportBound (max buffers (code.lower port).memBound) ∧ between.WellFormed ∧
          ((code.lower port).staticWords registers buffers : Int) + between.liveMem (max buffers (code.lower port).memBound) ≤
            words + 4 * slots + registers + 3 * buffers + before.liveMem buffers + time := by
  classical
  exact refined.restrict.resources bounded.restrict stored names tape ⟨value, valid⟩ before holds
    registers buffers initialRegisters initialBuffers finished reached

end Signatures.Runtime.CaliperBackend.Interactive
