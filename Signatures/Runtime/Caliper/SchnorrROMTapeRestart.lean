import Signatures.Runtime.Caliper.SchnorrROMTapeRestartPrepare
import Signatures.Runtime.Caliper.SchnorrROMTapeResetBounds

/-! Complete restart from a selected slot, scalar and retained state. Packet
preparation, tape scanning, reversal and both installed copies are executed and
charged. No prepared challenge cell or completed restart budget is assumed. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Restart
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

theorem scalarCell_budget :
    (Fresh.scalarCell layout).budget.time = 156 * layout.scalar.representation.encoding.words + 84 ∧
    (Fresh.scalarCell layout).budget.words = 507 * layout.scalar.representation.encoding.words + 550 := by
  constructor
  · change 8 * 1 + (0 + 8 * 1 + 52 * _ + 36 * _ + 16 * 1) +
      52 * _ + 36 * 1 + 16 * (layout.scalar.representation.encoding.words + 1) = _
    omega
  · change (26 * 1 + 14) + (1 + (26 * 1 + 14) + 169 * _ + 117 * _ + 52 * 1 + 124) +
      169 * _ + 117 * 1 + 52 * (layout.scalar.representation.encoding.words + 1) + 124 = _
    omega

theorem inputCell_budget :
    (inputCell layout).budget.time ≤ 188 * layout.width + 84 ∧
    (inputCell layout).budget.words ≤ 611 * layout.width + 680 := by
  have scalar := layout.entry_le
  rw [Layouts.entry_words] at scalar
  have tailSize := tail_le layout
  obtain ⟨scalarTime, scalarWords⟩ := scalarCell_budget layout
  change (8 * (tail layout).representation.encoding.words + 8 * layout.scalar.representation.encoding.words) +
      (Fresh.scalarCell layout).budget.time ≤ _ ∧
    ((26 * (tail layout).representation.encoding.words + 14) +
      (26 * layout.scalar.representation.encoding.words + 14) + 1) +
      (Fresh.scalarCell layout).budget.words + 1 ≤ _
  omega

theorem inputSaved_budget :
    (inputSaved layout).budget.time ≤ 48 * layout.width ∧
    (inputSaved layout).budget.words ≤ 156 * layout.width + 44 := by
  have tailSize := tail_le layout
  have tapesSize := Read.tapes_le layout
  have listSize := Read.list_le layout
  change (8 * (tail layout).representation.encoding.words + 8 * (Read.tapes layout).representation.encoding.words) +
      8 * (Read.list layout).representation.encoding.words ≤ _ ∧
    ((26 * (tail layout).representation.encoding.words + 14) +
      (26 * (Read.tapes layout).representation.encoding.words + 14) + 1) +
      (26 * (Read.list layout).representation.encoding.words + 14) + 1 ≤ _
  omega

theorem preparedTail_budget :
    (preparedTail layout).budget.time ≤ 496 * layout.width + 84 ∧
    (preparedTail layout).budget.words ≤ 1612 * layout.width + 848 := by
  obtain ⟨cellTime, cellWords⟩ := inputCell_budget layout
  obtain ⟨savedTime, savedWords⟩ := inputSaved_budget layout
  have inputSize := input_le layout
  have entrySize := layout.entry_le
  have listSize := Read.list_le layout
  change (inputCell layout).budget.time + (inputSaved layout).budget.time +
      52 * (input layout).representation.encoding.words + 36 * layout.entry.representation.encoding.words +
      16 * (Read.list layout).representation.encoding.words ≤ _ ∧
    (inputCell layout).budget.words + (inputSaved layout).budget.words +
      169 * (input layout).representation.encoding.words + 117 * layout.entry.representation.encoding.words +
      52 * (Read.list layout).representation.encoding.words + 124 ≤ _
  omega

theorem prepare_budget :
    (prepare layout).budget.time ≤ 800 * layout.width + 200 ∧
    (prepare layout).budget.words ≤ 2500 * layout.width + 1200 := by
  obtain ⟨tailTime, tailWords⟩ := preparedTail_budget layout
  have inputSize := input_le layout
  have tailSize := layout.resetTail_le
  change 8 * 1 + (preparedTail layout).budget.time +
      52 * (input layout).representation.encoding.words + 36 * 1 +
      16 * layout.resetTail.representation.encoding.words ≤ _ ∧
    (26 * 1 + 14) + (preparedTail layout).budget.words +
      169 * (input layout).representation.encoding.words + 117 * 1 +
      52 * layout.resetTail.representation.encoding.words + 124 ≤ _
  omega

def reset : Constructed layout.resetInput layout.replay
    (fun value => Schnorr.LazySeed.State.fromTape (Schnorr.SeedTape.reset 1 value.1 value.2.1 value.2.2)) where
  implementation := SchnorrROMTape.implementation layout
  budget := ⟨SchnorrROMTape.timeBudget layout, SchnorrROMTape.codeBudget layout⟩
  bounded := SchnorrROMTape.bounded layout
  buffers := 6
  buffers_le := SchnorrROMTape.buffers layout
  names := SchnorrROMTape.names layout

def source (value : Input F) : Schnorr.RawTape.State F :=
  Schnorr.RawTape.restart value.1 value.2.1 ⟨value.2.2.1, value.2.2.2⟩
def constructed : Constructed (input layout) layout.replay source :=
  ((prepare layout).then (reset layout)).castFunction rfl
def implementation := (constructed layout).implementation
def timeBudget : Nat := 800 * layout.width + 200 + SchnorrROMTape.timeBudget layout
def codeBudget : Nat := 2500 * layout.width + 1201 + SchnorrROMTape.codeBudget layout

theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  apply (constructed layout).bounded.mono
  · change (prepare layout).budget.time + SchnorrROMTape.timeBudget layout ≤ _
    have := (prepare_budget layout).1
    dsimp only [timeBudget]
    omega
  · change (prepare layout).budget.words + SchnorrROMTape.codeBudget layout + 1 ≤ _
    have := (prepare_budget layout).2
    dsimp only [codeBudget]
    omega

theorem buffers : (implementation layout).program.code.memBound ≤ 6 := by
  have bound := (constructed layout).buffers_le
  change (implementation layout).program.code.memBound ≤ max (prepare layout).buffers 6 at bound
  simpa only [prepare_buffers, Nat.max_self] using bound

theorem source_rawInput (slot : Nat) (answer : F) (state : Schnorr.RawTape.State F) :
    source (rawInput slot answer state) = Schnorr.RawTape.restart slot answer state := rfl

/-- The same actual execution implements the original restart and obeys its
complete bound, including preparation and the old state in initial memory. -/
theorem resources (slot : Nat) (answer : F) (state : Schnorr.RawTape.State F)
    (valid : (input layout).valid (rawInput slot answer state))
    (tape : RandomTape w) (before : State w)
    (holds : (input layout).representation.Holds ⟨rawInput slot answer state, valid⟩ before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time ⟨rawInput slot answer state, valid⟩) net peak ∧
      layout.replay.representation.Holds
        ⟨Schnorr.RawTape.restart slot answer state, (implementation layout).preserves _ valid⟩ after ∧
      (implementation layout).program.time ⟨rawInput slot answer state, valid⟩ ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (implementation layout).program.code)) ∧
        between.SupportBound (max buffers (implementation layout).program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
            5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  simpa only [source_rawInput, Nat.cast_zero, mul_zero, add_zero] using (bounded layout).memoryBound ((constructed layout).names 0)
    tape ⟨rawInput slot answer state, valid⟩ before holds registers buffers initialRegisters initialBuffers

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Restart
