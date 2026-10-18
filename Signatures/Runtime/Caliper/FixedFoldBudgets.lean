import Signatures.Runtime.Caliper.SourceFold
import Signatures.Runtime.Caliper.ImplementationBounds

/-! Uniform source-level budgets for folds with a fixed accumulator layout. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.FoldImplementation

open Caliper

variable {w : Nat} {A B E : Type}

theorem compile_boundedBy (entry : Layout w A) (state : Layout w B) (env : Layout w E)
    (argFits : entry.representation.encoding.words + state.representation.encoding.words + env.representation.encoding.words < 2 ^ w)
    {f : A × (B × E) → B} (body : Implementation .unit (bodyInput entry state env argFits) state f)
    (hw : 16 < 2 ^ w) (nameFits : body.program.savedBuffer < 2 ^ w) (capacity : Nat) (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    (bodyTime bodyWords : Nat) (bounded : body.BoundedBy bodyTime bodyWords) :
    (compile entry state env argFits body (by decide) hw nameFits capacity countFits fits).BoundedBy
      (8 * state.representation.encoding.words + capacity * (bodyTime + 44 * ListFold.width entry.representation.encoding.words
        state.representation.encoding.words env.representation.encoding.words capacity + 7))
      (26 * state.representation.encoding.words + 14 + capacity * (bodyWords + 169 * ListFold.width entry.representation.encoding.words
        state.representation.encoding.words env.representation.encoding.words capacity + 115)) := by
  constructor
  · intro value
    exact ListFold.time_unit_le (w := w) (liftedBody entry state env argFits body)
      (bodyRealizer entry state env argFits body).time bodyTime
      (fun value => bounded.time_le ⟨(value.1.val, value.2.1.val, value.2.2.val),
        value.1.property, value.2.1.property, value.2.2.property⟩)
      body.program.savedBuffer entry.representation.encoding.words state.representation.encoding.words env.representation.encoding.words
      capacity (view entry state env capacity countFits fits value).1.val
      (view entry state env capacity countFits fits value).2.1 (view entry state env capacity countFits fits value).2.2
  · exact (ListFold.code_descriptionWords_le body.program.code body.program.savedBuffer
      entry.representation.encoding.words state.representation.encoding.words env.representation.encoding.words capacity).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left capacity (by have h := bounded.code_le; omega)) _)

end Signatures.Runtime.CaliperBackend.BoundedSource.FoldImplementation
