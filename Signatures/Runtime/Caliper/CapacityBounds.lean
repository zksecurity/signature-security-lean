import Signatures.Runtime.Caliper.WordFrames
import Signatures.Runtime.Caliper.WordAcceptance

/-! Buffer capacities stay representable throughout accepted execution. Dynamic
allocations take their capacity from a word; static allocations are checked in
the program description. Together with well-formedness this also bounds lengths.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

def CapacitiesFit (state : State w) : Prop := ∀ buffer, state.caps buffer < 2 ^ w

def AllocationsFit : Stmt w → Prop
  | .memAllocI _ capacity => capacity < 2 ^ w
  | .seq first second | .ifNZ _ first second | .whileNZ first _ second => AllocationsFit first ∧ AllocationsFit second
  | _ => True

theorem DescriptionFits.allocationsFit {code : Stmt w} (fits : DescriptionFits code) : AllocationsFit code := by
  induction code with
  | memAllocI buffer capacity => exact fits capacity (by simp [description])
  | seq first second ih₁ ih₂ =>
    exact ⟨ih₁ (fun token member => fits token (by simp [description, member])),
      ih₂ (fun token member => fits token (by simp [description, member]))⟩
  | ifNZ condition first second ih₁ ih₂ | whileNZ first condition second ih₁ ih₂ =>
    exact ⟨ih₁ (fun token member => fits token (by simp [description, member])),
      ih₂ (fun token member => fits token (by simp [description, member]))⟩
  | _ => trivial

theorem CapacitiesFit.allocBuf {before : State w} (fits : CapacitiesFit before) (buffer capacity : Nat)
    (bound : capacity < 2 ^ w) : CapacitiesFit (before.allocBuf buffer capacity) := by
  intro other
  by_cases same : other = buffer
  · subst other; simpa using bound
  · simpa [same] using fits other

theorem capacities_preserved {cost : CostModel} {tape : RandomTape w} {code : Stmt w}
    {before after : State w} {time : Nat} {net peak : Int}
    (execution : Caliper.Exec cost tape code before after time net peak)
    (accepted : AllocationsFit code) (initial : CapacitiesFit before) : CapacitiesFit after := by
  induction execution with
  | skip | imm | rand | mov | un | bin | memLen | memLoad | memStore | memPush | memPop => exact initial
  | seq _ _ ih₁ ih₂ => exact ih₂ accepted.2 (ih₁ accepted.1 initial)
  | memAlloc => exact initial.allocBuf _ _ (BitVec.isLt _)
  | memAllocI => exact initial.allocBuf _ _ accepted
  | memFree => exact initial.allocBuf _ _ (by positivity)
  | ifNZ_true _ _ ih => exact ih accepted.1 initial
  | ifNZ_false _ _ ih => exact ih accepted.2 initial
  | while_done _ _ ih => exact ih accepted.1 initial
  | while_step _ _ _ _ ihGuard ihBody ihLoop =>
    exact ihLoop accepted (ihBody accepted.2 (ihGuard accepted.1 initial))

theorem LocalReach.capacitiesFit {cost : CostModel} {tape : RandomTape w} {code : Stmt w}
    {before between : State w} (reached : Caliper.Reaches cost tape code before between)
    (accepted : AllocationsFit code) (initial : CapacitiesFit before) : CapacitiesFit between := by
  induction reached with
  | start => exact initial
  | seq_left _ ih | ifNZ_true _ _ ih | while_guard _ ih => exact ih accepted.1 initial
  | ifNZ_false _ _ ih => exact ih accepted.2 initial
  | seq_right first _ ih | while_body first _ _ ih => exact ih accepted.2 (capacities_preserved first accepted.1 initial)
  | while_loop guard _ body _ ih =>
    exact ih accepted (capacities_preserved body accepted.2 (capacities_preserved guard accepted.1 initial))

namespace WordIO

def Code.AllocationsFit : Code w → Prop
  | .compute code => CaliperBackend.AllocationsFit code
  | .read _ | .write _ | .invoke => True
  | .seq first second | .branch _ first second => first.AllocationsFit ∧ second.AllocationsFit

theorem Code.DescriptionFits.allocationsFit {code : Code w} (fits : code.DescriptionFits) : code.AllocationsFit := by
  induction code with
  | compute code =>
    exact CaliperBackend.DescriptionFits.allocationsFit
      (fun token member => fits token (by simp [Code.description, member]))
  | read | write | invoke => trivial
  | seq first second ih₁ ih₂ | branch condition first second ih₁ ih₂ =>
    exact ⟨ih₁ (fun token member => fits token (by simp [Code.description, member])),
      ih₂ (fun token member => fits token (by simp [Code.description, member]))⟩

variable {cost : Costs} {tape : RandomTape w} {code : Code w} {before after between : State w}
    {trace : List (Event w)} {time : Nat} {net peak : Int}

theorem Exec.capacitiesFit (execution : Exec cost tape code before after trace time net peak)
    (accepted : code.AllocationsFit) (initial : CapacitiesFit before) : CapacitiesFit after := by
  induction execution with
  | compute execution => exact capacities_preserved execution accepted initial
  | read | write | invoke => exact initial
  | seq _ _ ih₁ ih₂ => exact ih₂ accepted.2 (ih₁ accepted.1 initial)
  | branch_yes _ _ ih => exact ih accepted.1 initial
  | branch_no _ _ ih => exact ih accepted.2 initial

theorem Exec.Visits.capacitiesFit {execution : Exec cost tape code before after trace time net peak}
    (reached : execution.Visits between) (accepted : code.AllocationsFit) (initial : CapacitiesFit before) :
    CapacitiesFit between := by
  induction reached with
  | start => exact initial
  | finish execution => exact execution.capacitiesFit accepted initial
  | compute _ reached => exact LocalReach.capacitiesFit reached accepted initial
  | seq_left _ _ _ ih | branch_yes _ _ _ ih => exact ih accepted.1 initial
  | branch_no _ _ _ ih => exact ih accepted.2 initial
  | seq_right first _ _ ih => exact ih accepted.2 (first.capacitiesFit accepted.1 initial)

/-- Every descriptor length and capacity is a word-sized natural at every
visited state of an accepted program, including inside local machine loops. -/
theorem Exec.Visits.descriptorsFit {execution : Exec cost tape code before after trace time net peak}
    (reached : execution.Visits between) (accepted : code.DescriptionFits)
    (initial : CapacitiesFit before) (wellFormed : before.WellFormed) :
    ∀ buffer, (between.bufs buffer).size ≤ between.caps buffer ∧ between.caps buffer < 2 ^ w := by
  intro buffer
  exact ⟨(reached.wellFormed wellFormed).size_le_cap buffer,
    reached.capacitiesFit accepted.allocationsFit initial buffer⟩

end WordIO
end Signatures.Runtime.CaliperBackend
