import Signatures.Runtime.Caliper.FoldStepBounds
import Signatures.Runtime.Caliper.SourceFold

/-! A source fold stage with distinct current/next accumulator layouts. Its
continuation and early return are executed implementations. Erasure recovers
ordinary source `List.foldl`, with no subtype witnesses stored in memory. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold

open Caliper

variable {w : Nat} {A B E : Type}

def frameView (entry : Layout w A) (state : Layout w B) (env : Layout w E) (capacity : Nat)
    (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w) :
    (FoldImplementation.input entry state env capacity countFits fits).Value ≃
      (BoundedList entry.Value capacity × (state.Value × env.Value)) :=
  (productView (entry.boundedList capacity countFits (by omega)) (state.prod env (by omega))).trans
    ((listView entry capacity).prodCongr (productView state env))

def bodyView {cost : CostModel} (entry : Layout w A) (state next : Layout w B) (env : Layout w E)
    (fits : entry.representation.encoding.words + state.representation.encoding.words + env.representation.encoding.words < 2 ^ w)
    {f : A × (B × E) → B} (body : Implementation cost (FoldImplementation.bodyInput entry state env fits) next f) :
    Realizer cost (ListFold.argument entry.representation state.representation env.representation fits) next.representation
      (fun value => ⟨f (value.1.val, value.2.1.val, value.2.2.val),
        body.preserves _ ⟨value.1.property, value.2.1.property, value.2.2.property⟩⟩) :=
  body.program.viewInput _
    (fun value : entry.Value × (state.Value × env.Value) =>
      ⟨(value.1.val, value.2.1.val, value.2.2.val), value.1.property, value.2.1.property, value.2.2.property⟩)
    (fun _ => rfl)

def frameResult {cost : CostModel} (entry : Layout w A) (state result : Layout w B) (env : Layout w E)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    {f : A × (B × E) → B}
    (following : Implementation cost (FoldImplementation.input entry state env capacity countFits fits) result (FoldImplementation.sourceFold f))
    (value : BoundedList entry.Value capacity × (state.Value × env.Value)) : result.Value :=
  let source := (frameView entry state env capacity countFits fits).symm value
  ⟨FoldImplementation.sourceFold f source.val, following.preserves source.val source.property⟩

def frameRealizer {cost : CostModel} (entry : Layout w A) (state result : Layout w B) (env : Layout w E)
    (capacity : Nat) (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    {f : A × (B × E) → B}
    (following : Implementation cost (FoldImplementation.input entry state env capacity countFits fits) result (FoldImplementation.sourceFold f)) :
    Realizer cost (ListFold.frame entry.representation state.representation env.representation capacity countFits fits) result.representation
      (frameResult entry state result env capacity countFits fits following) :=
  following.program.viewInput _ (frameView entry state env capacity countFits fits).symm (by
    intro value
    change _ = (ListFold.frame entry.representation state.representation env.representation capacity countFits fits).encoding.encode
      ((frameView entry state env capacity countFits fits) ((frameView entry state env capacity countFits fits).symm value))
    exact congrArg _ ((frameView entry state env capacity countFits fits).apply_symm_apply value).symm)

variable {cost : CostModel} (entry : Layout w A) (state next result : Layout w B) (env : Layout w E)
    (capacity : Nat) (hw : 16 < 2 ^ w) (countFits : capacity + 1 < 2 ^ w)
    (argFits : entry.representation.encoding.words + state.representation.encoding.words + env.representation.encoding.words < 2 ^ w)
    (inputFits : 1 + (capacity + 1) * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    (nextFits : 1 + capacity * entry.representation.encoding.words + next.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    {f : A × (B × E) → B}
    (body : Implementation cost (FoldImplementation.bodyInput entry state env argFits) next f)
    (following : Implementation cost (FoldImplementation.input entry next env capacity (by omega) nextFits) result (FoldImplementation.sourceFold f))
    (stop : Implementation cost state result id)

def stepResult (value : BoundedList entry.Value (capacity + 1) × (state.Value × env.Value)) : result.Value :=
  FoldStep.result
    (fun value => ⟨f (value.1.val, value.2.1.val, value.2.2.val), body.preserves _ ⟨value.1.property, value.2.1.property, value.2.2.property⟩⟩)
    (frameResult entry next result env capacity (by omega) nextFits following)
    (fun value => ⟨value.val, stop.preserves value.val value.property⟩) value

theorem stepResult_value (value : BoundedList entry.Value (capacity + 1) × (state.Value × env.Value)) :
    (stepResult entry state next result env capacity countFits argFits nextFits body following stop value).val =
      (value.1.val.map Subtype.val).foldl (fun accumulator head => f (head, accumulator, value.2.2.val)) value.2.1.val := by
  rcases value with ⟨⟨values, valid⟩, accumulator, context⟩
  cases values <;> rfl

theorem source_result (value : (FoldImplementation.input entry state env (capacity + 1) countFits inputFits).Value) :
    (stepResult entry state next result env capacity countFits argFits nextFits body following stop
      (frameView entry state env (capacity + 1) countFits inputFits value)).val = FoldImplementation.sourceFold f value.val := by
  rw [stepResult_value]
  change ((listView entry (capacity + 1) ⟨value.val.1, value.property.1⟩).val.map Subtype.val).foldl
    (fun accumulator head => f (head, accumulator, value.val.2.2)) value.val.2.1 = _
  rw [listView_values]
  rfl

def step (allocation : 1 ≤ cost.allocPerWord) (nameFits : body.program.savedBuffer < 2 ^ w) :
    Implementation cost (FoldImplementation.input entry state env (capacity + 1) countFits inputFits) result (FoldImplementation.sourceFold f) where
  preserves value valid := by
    rw [← source_result entry state next result env capacity countFits argFits inputFits nextFits body following stop ⟨value, valid⟩]
    exact (stepResult entry state next result env capacity countFits argFits nextFits body following stop
      (frameView entry state env (capacity + 1) countFits inputFits ⟨value, valid⟩)).property
  program :=
    ((FoldStep.realizer cost allocation entry.representation state.representation next.representation env.representation result.representation
      capacity hw countFits argFits inputFits nextFits (bodyView entry state next env argFits body)
      (frameRealizer entry next result env capacity (by omega) nextFits following) stop.program nameFits).viewInput _
      (frameView entry state env (capacity + 1) countFits inputFits) (fun _ => rfl)).viewOutput _ _ (by
        intro value
        apply congrArg result.representation.encoding.encode
        apply Subtype.ext
        exact (source_result entry state next result env capacity countFits argFits inputFits nextFits body following stop value).symm)

end Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold
