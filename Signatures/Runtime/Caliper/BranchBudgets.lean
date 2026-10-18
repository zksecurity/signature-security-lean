import Signatures.Runtime.Caliper.DataBudgets

/-! Uniform budgets for stored-tag dispatch and compiled source conditionals. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper

variable {w : Nat} {A B D : Type}

theorem Implementation.branch_boundedBy {left : Layout w A} {right : Layout w B} {output : Layout w D}
    {f : A → D} {g : B → D} (first : Implementation .unit left output f) (second : Implementation .unit right output g)
    (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words < 2 ^ w)
    (firstTime firstWords secondTime secondWords : Nat)
    (firstBound : first.BoundedBy firstTime firstWords) (secondBound : second.BoundedBy secondTime secondWords) :
    (first.branch second (by decide) hw fits).BoundedBy
      (firstTime + secondTime + 8 * max left.representation.encoding.words right.representation.encoding.words + 2)
      (firstWords + secondWords + 26 * left.representation.encoding.words + 26 * right.representation.encoding.words + 37) := by
  constructor
  · rintro ⟨value, valid⟩
    cases value with
    | inl value =>
      have bound := firstBound.time_le ⟨value, valid⟩
      have width := Nat.le_max_left left.representation.encoding.words right.representation.encoding.words
      change 1 + (1 + ((selectSlice (w := w) 1 left.representation.encoding.words).staticTime .unit + first.program.time ⟨value, valid⟩)) ≤ _
      simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
      omega
    | inr value =>
      have bound := secondBound.time_le ⟨value, valid⟩
      have width := Nat.le_max_right left.representation.encoding.words right.representation.encoding.words
      change 1 + (1 + ((selectSlice (w := w) 1 right.representation.encoding.words).staticTime .unit + second.program.time ⟨value, valid⟩)) ≤ _
      simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
      omega
  · change descriptionWords (Dispatch.code first.program.code second.program.code _ _) ≤ _
    rw [Dispatch.code_descriptionWords]
    have h₁ := firstBound.code_le
    have h₂ := secondBound.code_le
    omega

theorem Implementation.checkedBranch_boundedBy {input : Layout w A} {output : Layout w B} {hw : 16 < 2 ^ w}
    {condition : A → Bool} {yes no : A → B}
    (test : Implementation .unit input (DataImplementation.boolLayout w (width_pos hw)) condition)
    (left : Implementation .unit input output yes) (right : Implementation .unit input output no)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (tagFits : 1 + input.representation.encoding.words < 2 ^ w)
    (testTime testWords leftTime leftWords rightTime rightWords : Nat)
    (testBound : test.BoundedBy testTime testWords) (leftBound : left.BoundedBy leftTime leftWords)
    (rightBound : right.BoundedBy rightTime rightWords)
    (implementation : Implementation .unit input output (fun value => if condition value = true then yes value else no value))
    (compiled : test.checkedBranch (hw := hw) left right (by decide) duplicateFits tagFits = some implementation) :
    implementation.BoundedBy (testTime + leftTime + rightTime + 76 * input.representation.encoding.words + 43)
      (testWords + leftWords + rightWords + 273 * input.representation.encoding.words + 304) := by
  dsimp only [Implementation.checkedBranch] at compiled
  erw [Option.bind_eq_some_iff] at compiled
  obtain ⟨frame, frameEq, compiled⟩ := compiled
  cases Option.some.inj compiled
  have paired := Implementation.checkedPair_boundedBy test (Implementation.identity input (width_pos hw)) hw
    duplicateFits tagFits tagFits testTime testWords 0 1 testBound
    (Implementation.identity_boundedBy input (width_pos hw)) frame frameEq
  have selected := paired.then (DataImplementation.select_boundedBy input hw tagFits)
  have dispatched := selected.then (Implementation.branch_boundedBy left right hw (by simpa using tagFits)
    leftTime leftWords rightTime rightWords leftBound rightBound)
  apply (dispatched.castFunction _).mono
  · change testTime + 0 + 52 * input.representation.encoding.words + 36 * 1 + 16 * input.representation.encoding.words + 5 +
      (leftTime + rightTime + 8 * max input.representation.encoding.words input.representation.encoding.words + 2) ≤ _
    rw [Nat.max_self]
    omega
  · change testWords + 1 + 169 * input.representation.encoding.words + 117 * 1 + 52 * input.representation.encoding.words + 124 + 23 + 1 +
      (leftWords + rightWords + 26 * input.representation.encoding.words + 26 * input.representation.encoding.words + 37) + 1 ≤ _
    omega

end Signatures.Runtime.CaliperBackend.BoundedSource
