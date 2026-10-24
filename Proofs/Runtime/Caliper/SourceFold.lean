import Proofs.Runtime.Caliper.ListFoldBounds
import Proofs.Runtime.Caliper.ListLayout

/-! Compilation of the original source list fold on a proved bounded domain.
Only its body implementation is supplied. The fold's code, capacity preservation,
and equality to the original source result are derived here. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.FoldImplementation

open Caliper

variable {w : Nat} {A B E : Type}

def bodyInput (entry : Layout w A) (state : Layout w B) (env : Layout w E)
    (fits : entry.representation.encoding.words + state.representation.encoding.words + env.representation.encoding.words < 2 ^ w) :
    Layout w (A × (B × E)) :=
  entry.prod (state.prod env (by omega)) (by
    change entry.representation.encoding.words + (state.representation.encoding.words + env.representation.encoding.words) < 2 ^ w
    omega)

def input (entry : Layout w A) (state : Layout w B) (env : Layout w E) (capacity : Nat)
    (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w) :
    Layout w (List A × (B × E)) :=
  (entry.boundedList capacity countFits (by omega)).prod (state.prod env (by omega)) (by
    change (1 + capacity * entry.representation.encoding.words) + (state.representation.encoding.words + env.representation.encoding.words) < 2 ^ w
    omega)

def view (entry : Layout w A) (state : Layout w B) (env : Layout w E) (capacity : Nat)
    (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    (value : (input entry state env capacity countFits fits).Value) :
    BoundedList entry.Value capacity × (state.Value × env.Value) :=
  (listView entry capacity ⟨value.val.1, value.property.1⟩,
    ⟨value.val.2.1, value.property.2.1⟩, ⟨value.val.2.2, value.property.2.2⟩)

def sourceFold (f : A × (B × E) → B) (value : List A × (B × E)) : B :=
  value.1.foldl (fun accumulator head => f (head, accumulator, value.2.2)) value.2.1

variable {cost : CostModel} (entry : Layout w A) (state : Layout w B) (env : Layout w E)
    (argFits : entry.representation.encoding.words + state.representation.encoding.words + env.representation.encoding.words < 2 ^ w)
    {f : A × (B × E) → B} (implementation : Implementation cost (bodyInput entry state env argFits) state f)

def liftedBody (value : entry.Value × (state.Value × env.Value)) : state.Value :=
  ⟨f (value.1.val, value.2.1.val, value.2.2.val),
    implementation.preserves _ ⟨value.1.property, value.2.1.property, value.2.2.property⟩⟩

def bodyRealizer :
    Realizer cost (ListFold.argument entry.representation state.representation env.representation argFits)
      state.representation (liftedBody entry state env argFits implementation) :=
  implementation.program.viewInput _
    (fun value : entry.Value × (state.Value × env.Value) =>
      ⟨(value.1.val, value.2.1.val, value.2.2.val), value.1.property, value.2.1.property, value.2.2.property⟩)
    (fun _ => rfl)

theorem fold_values (values : List entry.Value) (initial : state.Value) (context : env.Value) :
    (values.foldl (fun accumulator head => liftedBody entry state env argFits implementation (head, accumulator, context)) initial).val =
      (values.map Subtype.val).foldl (fun accumulator head => f (head, accumulator, context.val)) initial.val := by
  induction values generalizing initial with
  | nil => rfl
  | cons head tail ih =>
    simpa only [List.foldl_cons, List.map_cons, liftedBody] using ih (liftedBody entry state env argFits implementation (head, initial, context))

theorem source_result (capacity : Nat) (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    (value : (input entry state env capacity countFits fits).Value) :
    (ListFold.denote (liftedBody entry state env argFits implementation) (view entry state env capacity countFits fits value)).val =
      sourceFold f value.val := by
  unfold ListFold.denote
  rw [fold_values]
  change ((listView entry capacity ⟨value.val.1, value.property.1⟩).val.map Subtype.val).foldl
    (fun accumulator head => f (head, accumulator, value.val.2.2)) value.val.2.1 = _
  rw [listView_values]
  rfl

include implementation in
theorem preserves (capacity : Nat) (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    (value : List A × (B × E)) (valid : (input entry state env capacity countFits fits).valid value) :
    state.valid (sourceFold f value) := by
  rw [← source_result entry state env argFits implementation capacity countFits fits ⟨value, valid⟩]
  exact (ListFold.denote (liftedBody entry state env argFits implementation)
    (view entry state env capacity countFits fits ⟨value, valid⟩)).property

def compile (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w)
    (nameFits : implementation.program.savedBuffer < 2 ^ w) (capacity : Nat) (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w) :
    Implementation cost (input entry state env capacity countFits fits) state (sourceFold f) where
  preserves := preserves entry state env argFits implementation capacity countFits fits
  program :=
    ((ListFold.realizer cost allocation entry.representation state.representation env.representation argFits hw
      (bodyRealizer entry state env argFits implementation) nameFits capacity countFits fits).viewInput
        (input entry state env capacity countFits fits).representation (view entry state env capacity countFits fits) (fun _ => rfl)).viewOutput
      state.representation _ (by
        intro value
        apply congrArg state.representation.encoding.encode
        apply Subtype.ext
        exact (source_result entry state env argFits implementation capacity countFits fits value).symm)

end Signatures.Runtime.CaliperBackend.BoundedSource.FoldImplementation
