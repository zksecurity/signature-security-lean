import Proofs.Runtime.Caliper.SourceFoldStep

/-! A checked source fold with iteration-dependent accumulator layouts. Only
individual body implementations and value-preserving finish conversions are
supplied. The fold, early returns and capacity preservation are constructed. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold

open Caliper

variable {w : Nat} {A B E : Type} {cost : CostModel}

def finish (allocation : 1 ≤ cost.allocPerWord) (entry : Layout w A) (state result : Layout w B)
    (env : Layout w E) (hw : 16 < 2 ^ w)
    (fits : 1 + 0 * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    (stop : Implementation cost state result id) (f : A × (B × E) → B) :
    Implementation cost (FoldImplementation.input entry state env 0 (by positivity) fits) result (FoldImplementation.sourceFold f) where
  preserves value valid := by
    have empty : value.1 = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero valid.1.1)
    simpa [FoldImplementation.sourceFold, empty] using stop.preserves value.2.1 valid.2.1
  program := (((ListFold.finish cost allocation entry.representation state.representation env.representation 0 hw (by positivity) fits).then
    stop.program).viewInput _ (frameView entry state env 0 (by positivity) fits) (fun _ => rfl)).viewOutput _ _ (by
      intro value
      apply congrArg result.representation.encoding.encode
      apply Subtype.ext
      have empty : value.val.1 = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero value.property.1.1)
      change FoldImplementation.sourceFold f value.val = value.val.2.1
      simp [FoldImplementation.sourceFold, empty])

def compile (allocation : 1 ≤ cost.allocPerWord) (entry : Layout w A) (result : Layout w B)
    (env : Layout w E) (hw : 16 < 2 ^ w) (f : A × (B × E) → B)
    (capacity : Nat) (states : Fin (capacity + 1) → Layout w B)
    (countFits : capacity < 2 ^ w)
    (argFits : ∀ i : Fin capacity,
      entry.representation.encoding.words + (states i.castSucc).representation.encoding.words + env.representation.encoding.words < 2 ^ w)
    (frameFits : ∀ i : Fin (capacity + 1),
      1 + (capacity - i.val) * entry.representation.encoding.words + (states i).representation.encoding.words +
        2 * env.representation.encoding.words < 2 ^ w)
    (bodies : ∀ i : Fin capacity, Option (Implementation cost
      (FoldImplementation.bodyInput entry (states i.castSucc) env (argFits i)) (states i.succ) f))
    (stops : ∀ i : Fin (capacity + 1), Implementation cost (states i) result id) :
    Option (Implementation cost (FoldImplementation.input entry (states 0) env capacity countFits (frameFits 0))
      result (FoldImplementation.sourceFold f)) :=
  match capacity with
  | 0 => some (finish allocation entry (states 0) result env hw (frameFits 0) (stops 0) f)
  | capacity + 1 => do
      let body ← bodies 0
      let following ← compile allocation entry result env hw f capacity (fun i => states i.succ) (by omega)
        (fun i => argFits i.succ)
        (fun i => by simpa only [Fin.val_succ, Nat.add_sub_add_right] using frameFits i.succ)
        (fun i => bodies i.succ) (fun i => stops i.succ)
      if nameFits : body.program.savedBuffer < 2 ^ w then
        some (step entry (states 0) (states 1) result env capacity hw countFits (argFits 0) (frameFits 0)
          (by simpa only [Fin.val_one, Nat.add_sub_cancel_right] using frameFits 1)
          body following (stops 0) allocation nameFits)
      else none

end Signatures.Runtime.CaliperBackend.BoundedSource.StagedFold
