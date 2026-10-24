import Proofs.Runtime.Caliper.BoundedSource

/-! Uniform time and stored-program bounds for an executed source implementation.
The bounds range over every admitted input, not only one test execution. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper

variable {w : Nat} {A B D : Type} {cost : CostModel}
    {input : Layout w A} {middle : Layout w B} {output : Layout w D}
    {f : A → B} {g : B → D}

structure Implementation.BoundedBy (implementation : Implementation cost input middle f)
    (time words : Nat) : Prop where
  time_le : ∀ value, implementation.program.time value ≤ time
  code_le : descriptionWords implementation.program.code ≤ words

theorem Implementation.BoundedBy.mono {implementation : Implementation cost input middle f}
    {time words largerTime largerWords : Nat} (bound : implementation.BoundedBy time words)
    (time_le : time ≤ largerTime) (words_le : words ≤ largerWords) :
    implementation.BoundedBy largerTime largerWords :=
  ⟨fun value => (bound.time_le value).trans time_le, bound.code_le.trans words_le⟩

theorem Implementation.BoundedBy.then
    {first : Implementation cost input middle f} {second : Implementation cost middle output g}
    {firstTime firstWords secondTime secondWords : Nat}
    (left : first.BoundedBy firstTime firstWords) (right : second.BoundedBy secondTime secondWords) :
    (first.then second).BoundedBy (firstTime + secondTime) (firstWords + secondWords + 1) := by
  constructor
  · intro value
    exact Nat.add_le_add (left.time_le value) (right.time_le _)
  · change descriptionWords (first.program.code ;; second.program.code) ≤ _
    rw [descriptionWords_seq]
    have h₁ := left.code_le
    have h₂ := right.code_le
    omega

/-- The uniform budget bounds actual execution, including allocated buffer
growth. Initial memory and static machine metadata have their separate account. -/
theorem Implementation.BoundedBy.exec {implementation : Implementation cost input middle f}
    {time words : Nat} (bound : implementation.BoundedBy time words)
    (allocation : 1 ≤ cost.allocPerWord) (tape : RandomTape w) (value : input.Value)
    (before : State w) (represented : input.representation.Holds value before) :
    ∃ after net peak, Caliper.Exec cost tape implementation.program.code before after
      (implementation.program.time value) net peak ∧
      middle.representation.Holds ⟨f value.val, implementation.preserves value.val value.property⟩ after ∧
      implementation.program.time value ≤ time ∧ net ≤ (time : Int) ∧ peak ≤ time := by
  obtain ⟨after, net, peak, execution, outputValue, _, _⟩ := implementation.program.correct tape value before represented
  refine ⟨after, net, peak, execution, outputValue, bound.time_le value, ?_, ?_⟩
  · exact (execution.net_le_time allocation).trans (Int.ofNat_le.mpr (bound.time_le value))
  · exact (execution.peak_le_time allocation).trans (Int.ofNat_le.mpr (bound.time_le value))

end Signatures.Runtime.CaliperBackend.BoundedSource
