import Proofs.Runtime.Caliper.Constructed
import Proofs.Runtime.Caliper.ListSnocBounds

/-! Constructed storage operations and proved same-byte domain changes.
Capacity-changing append remains executed; only equal stored encodings may be
viewed without instructions. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.Constructed
open Caliper
variable {w : Nat} {A B : Type} {input : Layout w A} {output : Layout w B} {f : A → B}

def restrictInput (body : Constructed input output f) (predicate : A → Prop) [DecidablePred predicate] :
    Constructed (input.restrict predicate) output f where
  implementation := body.implementation.restrictInput predicate
  budget := body.budget
  bounded := body.bounded.restrictInput predicate
  buffers := body.buffers
  buffers_le := body.buffers_le
  names := body.names

def viewOutput (body : Constructed input output f) (target : Layout w B)
    (preserves : ∀ value, input.valid value → target.valid (f value))
    (sameBytes : ∀ value : input.Value,
      target.representation.encoding.encode ⟨f value.val, preserves value.val value.property⟩ =
        output.representation.encoding.encode ⟨f value.val, body.implementation.preserves value.val value.property⟩) :
    Constructed input target f where
  implementation :=
    { preserves := preserves
      program := body.implementation.program.viewOutput target.representation _ sameBytes }
  budget := body.budget
  bounded := ⟨body.bounded.time_le, body.bounded.code_le⟩
  buffers := body.buffers
  buffers_le := body.buffers_le
  names := body.names

def forget (input : Layout w A) (predicate : A → Prop) [DecidablePred predicate] (hw : 0 < w) :
    Constructed (input.restrict predicate) input id :=
  (identity (input.restrict predicate) hw).viewOutput input (fun _ valid => valid.1) (fun _ => rfl)

def select (input : Layout w A) (hw : 16 < 2 ^ w) (fits : 1 + input.representation.encoding.words < 2 ^ w) :
    Constructed ((DataImplementation.boolLayout w (width_pos hw)).prod input fits)
      (input.sum input (width_pos hw) (by simpa using fits)) Boolean.select where
  implementation := DataImplementation.select .unit input hw fits
  budget := ⟨5, 23⟩
  bounded := DataImplementation.select_boundedBy input hw fits
  buffers := 1
  buffers_le := CellArithmetic.buffers (w := w) 0 .eq 0
  names := CellArithmetic.names 0 .eq 0

def snoc (layout : ListSnoc.Layouts w A) : Constructed layout.input layout.list (fun value => value.2 ++ [value.1]) where
  implementation := ListSnoc.implementation layout
  budget := ⟨ListSnoc.timeBudget layout, ListSnoc.codeBudget layout⟩
  bounded := ListSnoc.bounded layout
  buffers := 4
  buffers_le := ListSnoc.buffers layout
  names := ListSnoc.names layout

end Signatures.Runtime.CaliperBackend.BoundedSource.Constructed
