import Proofs.Runtime.Caliper.SchnorrAGMFreshArithmetic

/-! Derived code, time and dense-name bounds for the fresh-entry arithmetic.
Only the field-addition routine supplies local budgets. -/
namespace Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
open Caliper BoundedSource Assembly
variable {w qH qS : Nat} {M F G : Type} [Zero F] [Add F] [DecidableEq F]
    (layout : Layouts w M F G qH qS) (zeroValid : layout.scalar.valid 0)
    (add : Implementation .unit layout.affine layout.scalar (fun value => value.1 + value.2))
    {slots : Nat} (addBuffers : add.program.code.memBound ≤ slots) (slotsFit : slots < 2 ^ w)

def arithmeticTime (addTime : Nat) : Nat := addTime + 300 * layout.scalar.representation.encoding.words + 140
def arithmeticWords (addWords : Nat) : Nat := addWords + 900 * layout.scalar.representation.encoding.words + 620

theorem arithmetic_time {addTime : Nat} (bounded : ∀ value, add.program.time value ≤ addTime)
    (value : Input layout) :
    (arithmetic layout zeroValid add addBuffers slotsFit).time value ≤ arithmeticTime layout addTime := by
  have prepared := code_time_unit_le (addOperands layout)
  rw [addOperands_length] at prepared
  have added := add.program.retain_time_unit_le (input layout) layout.wordFits
    (by have := layout.wordFits; change max 2 add.program.code.memBound < _; omega)
    (adding layout).fits (Fresh.added layout).fits (addValue layout value)
  have tested := (isZero layout zeroValid).retain_time_unit_le (input layout) layout.wordFits
    (by have := (zero_names layout zeroValid).buffers; have := layout.wordFits
        change max 2 (isZero layout zeroValid).code.memBound < _; omega)
    (Fresh.added layout).fits (flagged layout).fits
      (⟨(addValue layout value).1.val.1 + (addValue layout value).1.val.2,
        add.preserves _ (addValue layout value).1.property⟩, value)
  have testBound := zero_time layout zeroValid
    (⟨(addValue layout value).1.val.1 + (addValue layout value).1.val.2,
      add.preserves _ (addValue layout value).1.property⟩ : layout.scalar.Value)
  have merging := code_time_unit_le (mergeOperands layout)
  rw [mergeOperands_length] at merging
  have merged := (Boolean.or layout.wordFits).retain_time_unit_le (input layout) layout.wordFits
    (by change 2 < 2 ^ w; have := layout.wordFits; omega) (Fresh.merging layout).fits (flagged layout).fits
      ((value.2.val.2, decide (value.2.val.1.2 + value.1.val = 0)), value)
  have finished := code_time_unit_le (finishOperands layout)
  rw [finishOperands_length] at finished
  have primitive := bounded (addValue layout value).1
  change (holdAdd layout add addBuffers slotsFit).time (addValue layout value) ≤ _ at added
  change (holdZero layout zeroValid).time
    (⟨value.2.val.1.2 + value.1.val, add.preserves _ (addValue layout value).1.property⟩, value) ≤ _ at tested
  change (holdMerge layout).time
    ((value.2.val.2, decide (value.2.val.1.2 + value.1.val = 0)), value) ≤ _ at merged
  change (Assembly.code (addOperands layout)).staticTime .unit ≤
    8 * (layout.affine.representation.encoding.words + (input layout).encoding.words) at prepared
  change (Assembly.code (mergeOperands layout)).staticTime .unit ≤ 8 * (2 + (input layout).encoding.words) at merging
  change (Assembly.code (finishOperands layout)).staticTime .unit ≤
    8 * (layout.entry.representation.encoding.words + (layout.affine.representation.encoding.words + 1)) at finished
  simp only [Layouts.affine_words, Layouts.entry_words, input_words] at prepared added tested merged merging finished
  change _ ≤ _ + 8 * 2 + 8 * 1 + _ at merged
  rw [Boolean.or_time] at merged
  change _ ≤ _ + 8 * _ + 8 * 1 + _ at tested
  change (prepareAdd layout).time value ≤ _ at prepared
  change (prepareMerge layout).time (decide (value.2.val.1.2 + value.1.val = 0), value) ≤ _ at merging
  change (finish layout).time
    (value.2.val.2 || decide (value.2.val.1.2 + value.1.val = 0), value) ≤ _ at finished
  change _ + _ + _ + _ + _ + _ ≤ _
  dsimp only [arithmeticTime, Realizer.then, Function.comp_apply, addValue, mergeValue] at *
  dsimp only [prepareMerge, finish, Assembly.realizer, holdMerge, Realizer.retain,
    Boolean.or, Realizer.viewOutput, Realizer.viewInput, WordBinary.realizer] at merging merged finished ⊢
  omega

theorem arithmetic_words {addWords : Nat} (bounded : descriptionWords add.program.code ≤ addWords) :
    descriptionWords (arithmetic layout zeroValid add addBuffers slotsFit).code ≤ arithmeticWords layout addWords := by
  have prepared := code_descriptionWords_le (addOperands layout)
  rw [addOperands_length] at prepared
  have added := add.program.retain_descriptionWords_le (by decide) (input layout) layout.wordFits
    (by have := layout.wordFits; change max 2 add.program.code.memBound < _; omega)
    (adding layout).fits (Fresh.added layout).fits
  have tested := (isZero layout zeroValid).retain_descriptionWords_le (by decide) (input layout) layout.wordFits
    (by have := (zero_names layout zeroValid).buffers; have := layout.wordFits
        change max 2 (isZero layout zeroValid).code.memBound < _; omega)
    (Fresh.added layout).fits (flagged layout).fits
  have testBound := zero_words layout zeroValid
  have merging := code_descriptionWords_le (mergeOperands layout)
  rw [mergeOperands_length] at merging
  have merged := (Boolean.or layout.wordFits).retain_descriptionWords_le (by decide) (input layout) layout.wordFits
    (by change 2 < 2 ^ w; have := layout.wordFits; omega) (Fresh.merging layout).fits (flagged layout).fits
  have finished := code_descriptionWords_le (finishOperands layout)
  rw [finishOperands_length] at finished
  change _ ≤ 26 * (layout.affine.representation.encoding.words + (input layout).encoding.words) + 14 at prepared
  change _ ≤ 26 * (2 + (input layout).encoding.words) + 14 at merging
  change _ ≤ 26 * (layout.entry.representation.encoding.words + (layout.affine.representation.encoding.words + 1)) + 14 at finished
  change _ ≤ _ + 26 * 2 + 26 * 1 + _ + 39 at merged
  rw [Boolean.or_words] at merged
  change _ ≤ _ + 26 * _ + 26 * 1 + _ + 39 at tested
  simp only [Layouts.affine_words, Layouts.entry_words, input_words] at prepared added tested merged merging finished
  simp only [arithmetic, Realizer.viewOutput, Realizer.then, descriptionWords_seq]
  change descriptionWords (holdAdd layout add addBuffers slotsFit).code ≤ _ at added
  change descriptionWords (holdZero layout zeroValid).code ≤ _ at tested
  change descriptionWords (holdMerge layout).code ≤ _ at merged
  change descriptionWords (prepareAdd layout).code ≤ _ at prepared
  change descriptionWords (prepareMerge layout).code ≤ _ at merging
  change descriptionWords (finish layout).code ≤ _ at finished
  unfold arithmeticWords
  omega

theorem arithmetic_names (addNames : NamesBound add.program.code slots) :
    NamesBound (arithmetic layout zeroValid add addBuffers slotsFit).code (max 6 (slots + 1)) := by
  have prepared := code_names (addOperands layout) 1 (addOperands_sources layout)
  have added := Retain.code_names add.program.code (max 2 add.program.code.memBound)
    layout.affine.representation.encoding.words layout.scalar.representation.encoding.words (input layout).encoding.words
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have tested := Retain.code_names (isZero layout zeroValid).code (max 2 (isZero layout zeroValid).code.memBound)
    layout.scalar.representation.encoding.words 1 (input layout).encoding.words
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have merging := code_names (mergeOperands layout) 1 (mergeOperands_sources layout)
  have merged := Retain.code_names (Boolean.or layout.wordFits).code 2 2 1 (input layout).encoding.words
    (by decide) (by change 1 ≤ 2; omega)
  have finished := code_names (finishOperands layout) 1 (finishOperands_sources layout)
  have zeroNames := zero_names layout zeroValid
  have boolNames := Boolean.or_names layout.wordFits
  change registerSlots (prepareAdd layout).code ≤ 3 ∧ (prepareAdd layout).code.memBound ≤ 2 at prepared
  change registerSlots (prepareMerge layout).code ≤ 3 ∧ (prepareMerge layout).code.memBound ≤ 2 at merging
  change registerSlots (finish layout).code ≤ 3 ∧ (finish layout).code.memBound ≤ 2 at finished
  change registerSlots (holdAdd layout add addBuffers slotsFit).code ≤ max 3 (registerSlots add.program.code) ∧
    (holdAdd layout add addBuffers slotsFit).code.memBound ≤ max 2 add.program.code.memBound + 1 at added
  change registerSlots (holdZero layout zeroValid).code ≤ max 3 (registerSlots (isZero layout zeroValid).code) ∧
    (holdZero layout zeroValid).code.memBound ≤ max 2 (isZero layout zeroValid).code.memBound + 1 at tested
  change registerSlots (holdMerge layout).code ≤ max 3 (registerSlots (Boolean.or layout.wordFits).code) ∧
    (holdMerge layout).code.memBound ≤ 3 at merged
  rcases addNames with ⟨addRegisters, addMemory⟩
  constructor
  · change max (max (max (max (max _ _) _) _) _) _ ≤ _
    have a := added.1
    have b := tested.1
    have c := merged.1
    have z := zeroNames.registers
    have o := boolNames.registers
    omega
  · change max (max (max (max (max _ _) _) _) _) _ ≤ _
    have a := added.2
    have b := tested.2
    have c := merged.2
    have z := zeroNames.buffers
    omega

end Signatures.Runtime.CaliperBackend.SchnorrAGM.Fresh
