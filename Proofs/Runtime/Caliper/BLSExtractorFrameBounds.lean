import Proofs.Runtime.Caliper.BLSExtractorTransition

/-! Routing uses at most eight unit steps per output word, including both
copies and allocations. Stored code, dense names, and all visited buffer states
are charged. The initial storage still includes fields that a branch discards. -/
namespace Signatures.Runtime.CaliperBackend.BLSExtractorFrame
open Caliper BoundedSource Assembly
variable {w : Nat} {M G F R : Type} (layout : TokenEvaluation.Layouts w M G F R)

theorem prepare_time (value : (input layout).Value) :
    (prepare layout).time value ≤ 8 * (prepared layout).representation.encoding.words := by
  have bound := Assembly.code_time_unit_le (prepareOperands (w := w) (target layout).representation.encoding.words
    (coefficients layout).representation.encoding.words (table layout).representation.encoding.words (tokens layout).representation.encoding.words)
  rw [prepareOperands_length] at bound
  exact bound
theorem prepare_words : descriptionWords (prepare layout).code ≤ 26 * (prepared layout).representation.encoding.words + 14 := by
  have bound := Assembly.code_descriptionWords_le (prepareOperands (w := w) (target layout).representation.encoding.words
    (coefficients layout).representation.encoding.words (table layout).representation.encoding.words (tokens layout).representation.encoding.words)
  rw [prepareOperands_length] at bound
  exact bound
theorem prepare_names : registerSlots (prepare layout).code ≤ 3 ∧ (prepare layout).code.memBound ≤ 2 :=
  Assembly.code_names _ 1 (prepareOperands_names _ _ _ _)
theorem signature_time (value : (input layout).Value) :
    (selectSignature layout).time value ≤ 8 * (signatureInput layout).representation.encoding.words := by
  have bound := Assembly.code_time_unit_le (signatureOperands (w := w) (target layout).representation.encoding.words
    (coefficients layout).representation.encoding.words (table layout).representation.encoding.words (tokens layout).representation.encoding.words)
  rw [signatureOperands_length] at bound
  exact bound
theorem signature_words : descriptionWords (selectSignature layout).code ≤ 26 * (signatureInput layout).representation.encoding.words + 14 := by
  have bound := Assembly.code_descriptionWords_le (signatureOperands (w := w) (target layout).representation.encoding.words
    (coefficients layout).representation.encoding.words (table layout).representation.encoding.words (tokens layout).representation.encoding.words)
  rw [signatureOperands_length] at bound
  exact bound
theorem signature_names : registerSlots (selectSignature layout).code ≤ 3 ∧ (selectSignature layout).code.memBound ≤ 2 :=
  Assembly.code_names _ 1 (signatureOperands_names _ _ _ _)

variable (bls : BLSTokens.Layouts w M G F)
theorem transition_time (value : (returned bls.good).Value) :
    (transition bls).time value ≤ 8 * (BLSSignatureTail.goodInput bls (goodTailFits bls)).encoding.words := by
  have bound := Assembly.code_time_unit_le (transitionOperands (w := w) (scalar bls.good).representation.encoding.words
    (table bls.good).representation.encoding.words (target bls.good).representation.encoding.words (signature bls.good).representation.encoding.words)
  rw [transition_size] at bound
  exact bound
theorem transition_words : descriptionWords (transition bls).code ≤
    26 * (BLSSignatureTail.goodInput bls (goodTailFits bls)).encoding.words + 14 := by
  have bound := Assembly.code_descriptionWords_le (transitionOperands (w := w) (scalar bls.good).representation.encoding.words
    (table bls.good).representation.encoding.words (target bls.good).representation.encoding.words (signature bls.good).representation.encoding.words)
  rw [transition_size] at bound
  exact bound
theorem transition_names : registerSlots (transition bls).code ≤ 3 ∧ (transition bls).code.memBound ≤ 2 :=
  Assembly.code_names _ 1 (transitionOperands_names _ _ _ _)

private theorem copy_resources {A B : Type} {input : Representation w A} {output : Representation w B} {f : A → B}
    (body : Realizer .unit input output f)
    (timeBound : ∀ value, body.time value ≤ 8 * output.encoding.words)
    (workspace : ∀ value, body.workspace value = body.time value)
    (codeBound : descriptionWords body.code ≤ 26 * output.encoding.words + 14)
    (names : registerSlots body.code ≤ 3 ∧ body.code.memBound ≤ 2)
    (tape : RandomTape w) (value : A) (before : State w) (holds : input.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape body.code before after (body.time value) net peak ∧
      output.Holds (f value) after ∧ body.time value ≤ 8 * output.encoding.words ∧
      ∀ between, (Caliper.Reaches .unit tape body.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots body.code)) ∧
        between.SupportBound (max buffers body.code.memBound) ∧ between.WellFormed ∧
        (staticWords body.code registers buffers : Int) + between.liveMem (max buffers body.code.memBound) ≤
          34 * output.encoding.words + 14 + max registers 3 + 3 * max buffers 2 + before.liveMem buffers := by
  obtain ⟨after, net, peak, execution, result, _, peakBound⟩ := body.correct tape value before holds
  refine ⟨after, net, peak, execution, result, timeBound value, ?_⟩
  intro between visited
  obtain ⟨regs, bufs, wf, memory⟩ := LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1
  refine ⟨regs, bufs, wf, ?_⟩
  have staticBound : staticWords body.code registers buffers ≤
      26 * output.encoding.words + 14 + max registers 3 + 3 * max buffers 2 := by
    unfold staticWords
    omega
  rw [workspace] at peakBound
  have elapsed := timeBound value
  omega

theorem prepare_resources (tape : RandomTape w) (value : (input layout).Value) (before : State w)
    (holds : (input layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (prepare layout).code before after ((prepare layout).time value) net peak ∧
      (prepared layout).representation.Holds (prepareValue layout value) after ∧
      (prepare layout).time value ≤ 8 * (prepared layout).representation.encoding.words ∧
      ∀ between, (Caliper.Reaches .unit tape (prepare layout).code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (prepare layout).code)) ∧
        between.SupportBound (max buffers (prepare layout).code.memBound) ∧ between.WellFormed ∧
        (staticWords (prepare layout).code registers buffers : Int) + between.liveMem (max buffers (prepare layout).code.memBound) ≤
          34 * (prepared layout).representation.encoding.words + 14 + max registers 3 + 3 * max buffers 2 + before.liveMem buffers :=
  copy_resources (prepare layout) (prepare_time layout) (fun _ => rfl) (prepare_words layout) (prepare_names layout)
    tape value before holds registers buffers initialRegisters initialBuffers

theorem signature_resources (tape : RandomTape w) (value : (input layout).Value) (before : State w)
    (holds : (input layout).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (selectSignature layout).code before after ((selectSignature layout).time value) net peak ∧
      (signatureInput layout).representation.Holds (signatureValue layout value) after ∧
      (selectSignature layout).time value ≤ 8 * (signatureInput layout).representation.encoding.words ∧
      ∀ between, (Caliper.Reaches .unit tape (selectSignature layout).code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (selectSignature layout).code)) ∧
        between.SupportBound (max buffers (selectSignature layout).code.memBound) ∧ between.WellFormed ∧
        (staticWords (selectSignature layout).code registers buffers : Int) + between.liveMem (max buffers (selectSignature layout).code.memBound) ≤
          34 * (signatureInput layout).representation.encoding.words + 14 + max registers 3 + 3 * max buffers 2 + before.liveMem buffers :=
  copy_resources (selectSignature layout) (signature_time layout) (fun _ => rfl) (signature_words layout) (signature_names layout)
    tape value before holds registers buffers initialRegisters initialBuffers

theorem transition_resources (tape : RandomTape w) (value : (returned bls.good).Value) (before : State w)
    (holds : (returned bls.good).representation.Holds value before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (transition bls).code before after ((transition bls).time value) net peak ∧
      (BLSSignatureTail.goodInput bls (goodTailFits bls)).Holds (transitionValue bls value) after ∧
      (transition bls).time value ≤ 8 * (BLSSignatureTail.goodInput bls (goodTailFits bls)).encoding.words ∧
      ∀ between, (Caliper.Reaches .unit tape (transition bls).code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots (transition bls).code)) ∧
        between.SupportBound (max buffers (transition bls).code.memBound) ∧ between.WellFormed ∧
        (staticWords (transition bls).code registers buffers : Int) + between.liveMem (max buffers (transition bls).code.memBound) ≤
          34 * (BLSSignatureTail.goodInput bls (goodTailFits bls)).encoding.words + 14 + max registers 3 + 3 * max buffers 2 + before.liveMem buffers :=
  copy_resources (transition bls) (transition_time bls) (fun _ => rfl) (transition_words bls) (transition_names bls)
    tape value before holds registers buffers initialRegisters initialBuffers

end Signatures.Runtime.CaliperBackend.BLSExtractorFrame
