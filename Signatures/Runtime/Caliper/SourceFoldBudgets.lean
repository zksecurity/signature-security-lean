import Signatures.Runtime.Caliper.StagedFold
import Signatures.Runtime.Caliper.ImplementationBounds

/-! Uniform budgets for the source views of one fold stage and its final
conversion. Views have identical bytes and preserve the executed profiles. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold

open Caliper

variable {w : Nat} {A B E : Type}

theorem finish_boundedBy (entry : Layout w A) (state result : Layout w B) (env : Layout w E)
    (hw : 16 < 2 ^ w)
    (fits : 1 + 0 * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    (stop : Implementation .unit state result id) (f : A × (B × E) → B)
    (stopTime stopWords : Nat) (bounded : stop.BoundedBy stopTime stopWords) :
    (finish (by decide) entry state result env hw fits stop f).BoundedBy
      (8 * state.representation.encoding.words + stopTime)
      (26 * state.representation.encoding.words + 15 + stopWords) := by
  constructor
  · intro value
    have bound := bounded.time_le ⟨value.val.2.1, value.property.2.1⟩
    change (selectSlice (w := w) _ state.representation.encoding.words).staticTime .unit +
      stop.program.time ⟨value.val.2.1, value.property.2.1⟩ ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    omega
  · change descriptionWords (selectSlice (w := w) _ state.representation.encoding.words ;; stop.program.code) ≤ _
    rw [descriptionWords_seq, selectSlice_descriptionWords]
    have bound := bounded.code_le
    omega

variable (entry : Layout w A) (state next result : Layout w B) (env : Layout w E)
    (capacity : Nat) (hw : 16 < 2 ^ w) (countFits : capacity + 1 < 2 ^ w)
    (argFits : entry.representation.encoding.words + state.representation.encoding.words + env.representation.encoding.words < 2 ^ w)
    (inputFits : 1 + (capacity + 1) * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    (nextFits : 1 + capacity * entry.representation.encoding.words + next.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    {f : A × (B × E) → B}
    (body : Implementation .unit (FoldImplementation.bodyInput entry state env argFits) next f)
    (following : Implementation .unit (FoldImplementation.input entry next env capacity (by omega) nextFits) result (FoldImplementation.sourceFold f))
    (stop : Implementation .unit state result id) (nameFits : body.program.savedBuffer < 2 ^ w)

theorem step_boundedBy (bodyTime bodyWords followingTime followingWords stopTime stopWords : Nat)
    (bodyBounded : body.BoundedBy bodyTime bodyWords)
    (followingBounded : following.BoundedBy followingTime followingWords)
    (stopBounded : stop.BoundedBy stopTime stopWords) :
    (step entry state next result env capacity hw countFits argFits inputFits nextFits body following stop (by decide) nameFits).BoundedBy
      (bodyTime + followingTime + stopTime + 44 * FoldStep.width entry.representation.encoding.words
        state.representation.encoding.words next.representation.encoding.words env.representation.encoding.words capacity + 7)
      (bodyWords + followingWords + stopWords + 169 * FoldStep.width entry.representation.encoding.words
        state.representation.encoding.words next.representation.encoding.words env.representation.encoding.words capacity + 116) := by
  constructor
  · intro value
    exact FoldStep.time_unit_le (w := w)
      (fun value : entry.Value × (state.Value × env.Value) =>
        (⟨f (value.1.val, value.2.1.val, value.2.2.val),
          body.preserves _ ⟨value.1.property, value.2.1.property, value.2.2.property⟩⟩ : next.Value))
      (bodyView entry state next env argFits body).time
      (frameRealizer entry next result env capacity (by omega) nextFits following).time
      stop.program.time bodyTime followingTime stopTime
      (fun value => bodyBounded.time_le ⟨(value.1.val, value.2.1.val, value.2.2.val),
        value.1.property, value.2.1.property, value.2.2.property⟩)
      (fun value => followingBounded.time_le ((frameView entry next env capacity (by omega) nextFits).symm value))
      stopBounded.time_le body.program.savedBuffer entry.representation.encoding.words state.representation.encoding.words
      next.representation.encoding.words env.representation.encoding.words
      (frameView entry state env (capacity + 1) countFits inputFits value)
  · have bound := FoldStep.code_descriptionWords_le body.program.code following.program.code stop.program.code
      body.program.savedBuffer entry.representation.encoding.words state.representation.encoding.words
      next.representation.encoding.words env.representation.encoding.words capacity
    have hb := bodyBounded.code_le
    have hf := followingBounded.code_le
    have hs := stopBounded.code_le
    change descriptionWords (FoldStep.code body.program.code following.program.code stop.program.code
      body.program.savedBuffer entry.representation.encoding.words state.representation.encoding.words
      next.representation.encoding.words env.representation.encoding.words capacity) ≤ _
    omega

end Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold
