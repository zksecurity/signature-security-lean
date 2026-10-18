import Signatures.Runtime.Caliper.InteractiveBounds
import Signatures.Runtime.Caliper.Resources

/-! Physical buffer accounting for the word-I/O extension, with stored program,
register and descriptor reservations. Intermediate states belong to a particular
execution derivation: external replies from unrelated executions cannot be mixed.
This remains a machine account, separate from flat-memory/CPU adequacy.
-/

namespace Signatures.Runtime.CaliperBackend.WordIO

open Caliper

variable {w : Nat}

def Code.registerSlots : Code w → Nat
  | .compute code => CaliperBackend.registerSlots code
  | .read register | .write register => register + 1
  | .invoke => 0
  | .seq first second => max first.registerSlots second.registerSlots
  | .branch condition yes no => max (condition + 1) (max yes.registerSlots no.registerSlots)

theorem Code.writes_lt_registerSlots {code : Code w} {register : Reg}
    (written : code.Writes register) : register < code.registerSlots := by
  induction code with
  | compute code => exact CaliperBackend.writes_lt_registerSlots written
  | read destination => subst register; exact Nat.lt_succ_self _
  | write | invoke => cases written
  | seq first second ih₁ ih₂ =>
    exact written.elim (fun h => lt_of_lt_of_le (ih₁ h) (le_max_left _ _))
      (fun h => lt_of_lt_of_le (ih₂ h) (le_max_right _ _))
  | branch condition yes no ih₁ ih₂ =>
    exact written.elim (fun h => lt_of_lt_of_le (ih₁ h) ((le_max_left _ _).trans (le_max_right _ _)))
      (fun h => lt_of_lt_of_le (ih₂ h) ((le_max_right _ _).trans (le_max_right _ _)))

/-- Dense slots include gaps in static names. Each buffer reserves three words
for pointer, length and capacity, independently of its allocated contents. -/
def Code.staticWords (code : Code w) (initialRegisters initialBuffers : Nat) : Nat :=
  code.descriptionWords + max initialRegisters code.registerSlots + 3 * max initialBuffers code.memBound

variable {cost : Costs} {tape : RandomTape w} {code : Code w}
    {before after between : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}

theorem Exec.peak_nonneg (execution : Exec cost tape code before after trace time net peak) : 0 ≤ peak := by
  induction execution with
  | compute execution => exact execution.peak_nonneg
  | read | write | invoke => omega
  | seq _ _ ih₁ _ => exact ih₁.trans (le_max_left _ _)
  | branch_yes _ _ ih | branch_no _ _ ih => exact ih

theorem Exec.net_le_peak (execution : Exec cost tape code before after trace time net peak) : net ≤ peak := by
  induction execution with
  | compute execution => exact execution.net_le_peak
  | read | write | invoke => omega
  | seq _ _ _ ih₂ => omega
  | branch_yes _ _ ih | branch_no _ _ ih => exact ih

theorem Exec.liveMem_eq (execution : Exec cost tape code before after trace time net peak) {buffers : Nat}
    (names : ∀ buffer, code.Touches buffer → buffer < buffers) :
    (after.liveMem buffers : Int) = before.liveMem buffers + net := by
  induction execution with
  | compute execution => exact execution.liveMem_eq names
  | read => simp
  | write | invoke => simp
  | seq _ _ ih₁ ih₂ =>
    rw [ih₂ (fun b h => names b (.inr h)), ih₁ (fun b h => names b (.inl h))]
    ring
  | branch_yes _ _ ih => exact ih (fun b h => names b (.inl h))
  | branch_no _ _ ih => exact ih (fun b h => names b (.inr h))

theorem Exec.liveMem_le_peak (execution : Exec cost tape code before after trace time net peak) {buffers : Nat}
    (names : ∀ buffer, code.Touches buffer → buffer < buffers) :
    (after.liveMem buffers : Int) ≤ before.liveMem buffers + peak := by
  rw [execution.liveMem_eq names]
  have := execution.net_le_peak
  omega

theorem Exec.supportBound_preserved (execution : Exec cost tape code before after trace time net peak) {buffers : Nat}
    (names : ∀ buffer, code.Touches buffer → buffer < buffers) (initial : before.SupportBound buffers) :
    after.SupportBound buffers := by
  intro buffer outside
  rw [(execution.frame_buf (fun h => Nat.not_lt_of_ge outside (names buffer h))).2]
  exact initial buffer outside

theorem Exec.registerBound_preserved (execution : Exec cost tape code before after trace time net peak)
    {registers : Nat} (initial : RegisterBound before registers) :
    RegisterBound after (max registers code.registerSlots) := by
  intro register outside
  rw [execution.frame_reg (fun h => Nat.not_lt_of_ge ((le_max_right _ _).trans outside)
    (Code.writes_lt_registerSlots h))]
  exact initial register ((le_max_left _ _).trans outside)

/-- Instruction-boundary states in this exact I/O execution, including both
endpoints and the intermediate states of each embedded Caliper block. -/
inductive Exec.Visits : {code : Code w} → {before after : State w} → {trace : List (Event w)} →
    {time : Nat} → {net peak : Int} → Exec cost tape code before after trace time net peak → State w → Prop where
  | start {code : Code w} {before after : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
      (execution : Exec cost tape code before after trace time net peak) :
      Visits execution before
  | finish {code : Code w} {before after : State w} {trace : List (Event w)} {time : Nat} {net peak : Int}
      (execution : Exec cost tape code before after trace time net peak) :
      Visits execution after
  | compute {code : Stmt w} {before after between : State w} {time : Nat} {net peak : Int}
      (execution : Caliper.Exec cost.machine tape code before after time net peak)
      (reached : Caliper.Reaches cost.machine tape code before between) : Visits (.compute execution) between
  | seq_left {first second : Code w} {before middle after between : State w}
      {left right : List (Event w)} {t₁ t₂ : Nat} {d₁ d₂ p₁ p₂ : Int}
      (firstExec : Exec cost tape first before middle left t₁ d₁ p₁)
      (secondExec : Exec cost tape second middle after right t₂ d₂ p₂)
      (reached : Visits firstExec between) : Visits (.seq firstExec secondExec) between
  | seq_right {first second : Code w} {before middle after between : State w}
      {left right : List (Event w)} {t₁ t₂ : Nat} {d₁ d₂ p₁ p₂ : Int}
      (firstExec : Exec cost tape first before middle left t₁ d₁ p₁)
      (secondExec : Exec cost tape second middle after right t₂ d₂ p₂)
      (reached : Visits secondExec between) : Visits (.seq firstExec secondExec) between
  | branch_yes {condition : Reg} {yes no : Code w} {before after between : State w}
      {trace : List (Event w)} {time : Nat} {net peak : Int}
      (nonzero : before.regs condition ≠ 0) (execution : Exec cost tape yes before after trace time net peak)
      (reached : Visits execution between) : Visits (.branch_yes (no := no) nonzero execution) between
  | branch_no {condition : Reg} {yes no : Code w} {before after between : State w}
      {trace : List (Event w)} {time : Nat} {net peak : Int}
      (zero : before.regs condition = 0) (execution : Exec cost tape no before after trace time net peak)
      (reached : Visits execution between) : Visits (.branch_no (yes := yes) zero execution) between

theorem Exec.Visits.liveMem_le_peak {execution : Exec cost tape code before after trace time net peak}
    (reached : execution.Visits between) {buffers : Nat}
    (names : ∀ buffer, code.Touches buffer → buffer < buffers) :
    (between.liveMem buffers : Int) ≤ before.liveMem buffers + peak := by
  induction reached with
  | start execution => have := execution.peak_nonneg; omega
  | finish execution => exact execution.liveMem_le_peak names
  | compute execution reached => exact execution.reaches_liveMem_le_peak reached names
  | seq_left first second reached ih =>
    have := ih (fun b h => names b (.inl h))
    omega
  | seq_right first second reached ih =>
    have := ih (fun b h => names b (.inr h))
    have := first.liveMem_eq (fun b h => names b (.inl h))
    omega
  | branch_yes _ _ _ ih => exact ih (fun b h => names b (.inl h))
  | branch_no _ _ _ ih => exact ih (fun b h => names b (.inr h))

theorem Exec.total_memory_bound (execution : Exec cost tape code before after trace time net peak)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    RegisterBound after (max registers code.registerSlots) ∧
    after.SupportBound (max buffers code.memBound) ∧
    (code.staticWords registers buffers : Int) + after.liveMem (max buffers code.memBound) ≤
      code.staticWords registers buffers + before.liveMem (max buffers code.memBound) + peak := by
  have names : ∀ buffer, code.Touches buffer → buffer < max buffers code.memBound :=
    fun _ h => lt_of_lt_of_le (Code.touches_lt_memBound h) (le_max_right _ _)
  refine ⟨execution.registerBound_preserved initialRegisters,
    execution.supportBound_preserved names (initialBuffers.mono (le_max_left _ _)), ?_⟩
  have := execution.liveMem_le_peak names
  omega

theorem Exec.Visits.memory_bound {execution : Exec cost tape code before after trace time net peak}
    (reached : execution.Visits between) (registers buffers : Nat) :
    (code.staticWords registers buffers : Int) + between.liveMem (max buffers code.memBound) ≤
      code.staticWords registers buffers + before.liveMem (max buffers code.memBound) + peak := by
  have := reached.liveMem_le_peak (buffers := max buffers code.memBound)
    (fun _ h => lt_of_lt_of_le (Code.touches_lt_memBound h) (le_max_right _ _))
  omega

end Signatures.Runtime.CaliperBackend.WordIO
