import Signatures.Runtime.Caliper.SchnorrROMTapeReply

/-! Derived linear overhead and complete visited-memory bounds for actual
caller reply decoding. The original reply and both tapes are returned by the
same bounded execution. -/

namespace Signatures.Runtime.CaliperBackend.SchnorrROMTape.Reply
open Caliper BoundedSource
variable {w : Nat} {F : Type} (layout : Layouts w F)

theorem increment_budget : (increment layout).budget.time = 118 ∧ (increment layout).budget.words = 531 := by
  constructor <;> rfl

theorem inputNatural_budget :
    (inputNatural layout).budget.time ≤ 40 * layout.width + 8 ∧
    (inputNatural layout).budget.words ≤ 130 * layout.width + 85 := by
  have outputSize := response_le layout
  have entrySize := layout.entry_le
  have payloadSize : layout.payload.representation.encoding.words ≤ layout.width := by
    change 1 + layout.payload.representation.encoding.words ≤ layout.width at entrySize
    omega
  change (8 * (Read.output layout).representation.encoding.words +
    (8 * layout.entry.representation.encoding.words + 8 * layout.payload.representation.encoding.words + 8)) ≤ _ ∧
    (26 * (Read.output layout).representation.encoding.words + 14) +
      (((26 * layout.entry.representation.encoding.words + 14) +
        (26 * layout.payload.representation.encoding.words + 14) + 1) + 40 + 1) + 1 ≤ _
  omega

theorem divisor_budget : (divisor layout).budget.time = 126 ∧ (divisor layout).budget.words = 572 := by
  obtain ⟨elapsed, stored⟩ := increment_budget layout
  change 8 + (increment layout).budget.time = _ ∧ 40 + (increment layout).budget.words + 1 = _
  omega

theorem moduloInput_time : (moduloInput layout).budget.time ≤ 248 * layout.width + 186 := by
  have naturalTime := (inputNatural_budget layout).1
  have divisorTime := (divisor_budget layout).1
  have inputSize := input_le layout
  change (inputNatural layout).budget.time + (divisor layout).budget.time +
    52 * (input layout).representation.encoding.words + 36 * 1 + 16 * 1 ≤ _
  omega

theorem moduloInput_words : (moduloInput layout).budget.words ≤ 806 * layout.width + 950 := by
  have naturalWords := (inputNatural_budget layout).2
  have divisorWords := (divisor_budget layout).2
  have inputSize := input_le layout
  rw [moduloInput_budget]
  dsimp only [Budget.pair]
  omega

theorem answer_budget :
    (answer layout).budget.time ≤ 248 * layout.width + 192 ∧
    (answer layout).budget.words ≤ 806 * layout.width + 978 := by
  have elapsed := moduloInput_time layout
  have stored := moduloInput_words layout
  change (moduloInput layout).budget.time + 6 ≤ _ ∧ (moduloInput layout).budget.words + 27 + 1 ≤ _
  omega

theorem inputTapes_budget :
    (inputTapes layout).budget.time ≤ 40 * layout.width ∧
    (inputTapes layout).budget.words ≤ 130 * layout.width + 29 := by
  have outputSize := response_le layout
  have tapesSize := Read.tapes_le layout
  change 8 * (Read.output layout).representation.encoding.words + 8 * (Read.tapes layout).representation.encoding.words ≤ _ ∧
    (26 * (Read.output layout).representation.encoding.words + 14) +
      (26 * (Read.tapes layout).representation.encoding.words + 14) + 1 ≤ _
  omega

theorem finishedTail_budget :
    (finishedTail layout).budget.time ≤ 528 * layout.width + 228 ∧
    (finishedTail layout).budget.words ≤ 1716 * layout.width + 1248 := by
  obtain ⟨answerTime, answerWords⟩ := answer_budget layout
  obtain ⟨tapesTime, tapesWords⟩ := inputTapes_budget layout
  have inputSize := input_le layout
  have tapesSize := Read.tapes_le layout
  change (answer layout).budget.time + (inputTapes layout).budget.time +
      52 * (input layout).representation.encoding.words + 36 * 1 + 16 * (Read.tapes layout).representation.encoding.words ≤ _ ∧
    (answer layout).budget.words + (inputTapes layout).budget.words +
      169 * (input layout).representation.encoding.words + 117 * 1 +
      52 * (Read.tapes layout).representation.encoding.words + 124 ≤ _
  omega

def privateTime : Nat := 800 * layout.width + 300
def privateWords : Nat := 2600 * layout.width + 1600
theorem private_bounded :
    (privateDecoder layout).implementation.BoundedBy (privateTime layout) (privateWords layout) := by
  obtain ⟨tailTime, tailWords⟩ := finishedTail_budget layout
  have inputSize := input_le layout
  have tailSize := privateTail_le layout
  apply (privateDecoder layout).bounded.mono
  · change 8 + (finishedTail layout).budget.time + 52 * (input layout).representation.encoding.words +
      36 * 1 + 16 * (privateTail layout).representation.encoding.words ≤ _
    dsimp only [privateTime]
    omega
  · change 40 + (finishedTail layout).budget.words + 169 * (input layout).representation.encoding.words +
      117 * 1 + 52 * (privateTail layout).representation.encoding.words + 124 ≤ _
    dsimp only [privateWords]
    omega

def scalarTime : Nat := 300 * layout.width
def scalarWords : Nat := 900 * layout.width + 200
theorem scalar_bounded :
    (scalarDecoder layout).implementation.BoundedBy (scalarTime layout) (scalarWords layout) := by
  have outputSize := response_le layout
  have entrySize := layout.entry_le
  have tapesSize := Read.tapes_le layout
  have payloadSize : layout.payload.representation.encoding.words ≤ layout.width := by
    change 1 + layout.payload.representation.encoding.words ≤ layout.width at entrySize
    omega
  have scalarSize : layout.scalar.representation.encoding.words ≤ layout.width := by
    rw [Layouts.entry_words] at entrySize
    omega
  apply (scalarDecoder layout).bounded.mono
  · change ((8 * layout.entry.representation.encoding.words + 8 * layout.payload.representation.encoding.words) +
      8 * layout.scalar.representation.encoding.words) + 8 * (Read.tapes layout).representation.encoding.words +
      52 * (Read.output layout).representation.encoding.words + 36 * layout.scalar.representation.encoding.words +
      16 * (Read.tapes layout).representation.encoding.words ≤ _
    dsimp only [scalarTime]
    omega
  · change (((26 * layout.entry.representation.encoding.words + 14) +
      (26 * layout.payload.representation.encoding.words + 14) + 1) +
      (26 * layout.scalar.representation.encoding.words + 14) + 1) +
      (26 * (Read.tapes layout).representation.encoding.words + 14) +
      169 * (Read.output layout).representation.encoding.words + 117 * layout.scalar.representation.encoding.words +
      52 * (Read.tapes layout).representation.encoding.words + 124 ≤ _
    dsimp only [scalarWords]
    omega

theorem private_resources (n : Nat) (value : Read.Output F)
    (valid : (input layout).valid (n, value)) (tape : RandomTape w) (before : State w)
    (holds : (input layout).representation.Holds ⟨(n, value), valid⟩ before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (privateDecoder layout).implementation.program.code before after
      ((privateDecoder layout).implementation.program.time ⟨(n, value), valid⟩) net peak ∧
      (privateOutput layout).representation.Holds
        ⟨(n, (Schnorr.RawTape.decode (.inl n) value.1).val, value.2),
          (privateDecoder layout).implementation.preserves _ valid⟩ after ∧
      (privateDecoder layout).implementation.program.time ⟨(n, value), valid⟩ ≤ privateTime layout ∧
      ∀ between, (Caliper.Reaches .unit tape (privateDecoder layout).implementation.program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (privateDecoder layout).implementation.program.code)) ∧
        between.SupportBound (max buffers (privateDecoder layout).implementation.program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (privateDecoder layout).implementation.program.code registers buffers : Int) +
          between.liveMem (max buffers (privateDecoder layout).implementation.program.code.memBound) ≤
            5 * privateWords layout + registers + 3 * buffers + before.liveMem buffers + privateTime layout := by
  simpa only [private_source, Nat.cast_zero, mul_zero, add_zero] using
    (private_bounded layout).memoryBound ((privateDecoder layout).names 0)
      tape ⟨(n, value), valid⟩ before holds registers buffers initialRegisters initialBuffers

theorem scalar_resources (value : (Read.output layout).Value) (tape : RandomTape w) (before : State w)
    (holds : (Read.output layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (scalarDecoder layout).implementation.program.code before after
      ((scalarDecoder layout).implementation.program.time value) net peak ∧
      (scalarOutput layout).representation.Holds
        ⟨(Schnorr.RawTape.decode (.inr ()) value.val.1, value.val.2),
          (scalarDecoder layout).implementation.preserves value.val value.property⟩ after ∧
      (scalarDecoder layout).implementation.program.time value ≤ scalarTime layout ∧
      ∀ between, (Caliper.Reaches .unit tape (scalarDecoder layout).implementation.program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (scalarDecoder layout).implementation.program.code)) ∧
        between.SupportBound (max buffers (scalarDecoder layout).implementation.program.code.memBound) ∧ between.WellFormed ∧
        (staticWords (scalarDecoder layout).implementation.program.code registers buffers : Int) +
          between.liveMem (max buffers (scalarDecoder layout).implementation.program.code.memBound) ≤
            5 * scalarWords layout + registers + 3 * buffers + before.liveMem buffers + scalarTime layout := by
  simpa only [scalar_source, Nat.cast_zero, mul_zero, add_zero] using
    (scalar_bounded layout).memoryBound ((scalarDecoder layout).names 0)
      tape value before holds registers buffers initialRegisters initialBuffers

end Signatures.Runtime.CaliperBackend.SchnorrROMTape.Reply
