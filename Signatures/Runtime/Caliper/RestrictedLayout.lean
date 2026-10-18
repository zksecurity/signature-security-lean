import Signatures.Runtime.Caliper.DataBudgets

/-! Additional domain invariants without changing stored bytes. Deciding the
invariant is part of the mathematical decoder, never a machine instruction.
An executable operation on the restricted domain still needs actual code and
a preservation proof. Changes to padding or capacity require charged copying. -/

namespace Signatures.Runtime.CaliperBackend

variable {w : Nat} {A B : Type}

def Encoding.restrict (encoding : Encoding w A) (predicate : A → Prop) [DecidablePred predicate] :
    Encoding w {value : A // predicate value} where
  words := encoding.words
  encode value := encoding.encode value.val
  decode bytes := do
    let value ← encoding.decode bytes
    if valid : predicate value then some ⟨value, valid⟩ else none
  encode_length value := encoding.encode_length value.val
  decode_encode value := by simp [encoding.decode_encode, value.property]
  decode_length bytes value decoded := by
    cases h : encoding.decode bytes with
    | none => simp [h] at decoded
    | some output => exact encoding.decode_length bytes output h

def Representation.restrict (representation : Representation w A) (predicate : A → Prop)
    [DecidablePred predicate] : Representation w {value : A // predicate value} :=
  ⟨representation.encoding.restrict predicate, representation.fits⟩

namespace BoundedSource

def restrictedView (layout : Layout w A) (predicate : A → Prop) :
    {value : A // layout.valid value ∧ predicate value} ≃ {value : layout.Value // predicate value.val} where
  toFun value := ⟨⟨value.val, value.property.1⟩, value.property.2⟩
  invFun value := ⟨value.val.val, value.val.property, value.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def Layout.restrict (layout : Layout w A) (predicate : A → Prop) [DecidablePred predicate] : Layout w A where
  valid value := layout.valid value ∧ predicate value
  representation := (layout.representation.restrict (fun value => predicate value.val)).transport (restrictedView layout predicate)

@[simp] theorem Layout.restrict_words (layout : Layout w A) (predicate : A → Prop) [DecidablePred predicate] :
    (layout.restrict predicate).representation.encoding.words = layout.representation.encoding.words := rfl

@[simp] theorem Layout.restrict_encode (layout : Layout w A) (predicate : A → Prop) [DecidablePred predicate]
    (value : (layout.restrict predicate).Value) :
    (layout.restrict predicate).representation.encoding.encode value =
      layout.representation.encoding.encode ⟨value.val, value.property.1⟩ := rfl

open Caliper

variable {cost : CostModel} {input : Layout w A} {output : Layout w B} {f : A → B}

def Implementation.restrictInput (body : Implementation cost input output f)
    (predicate : A → Prop) [DecidablePred predicate] : Implementation cost (input.restrict predicate) output f where
  preserves value valid := body.preserves value valid.1
  program := body.program.viewInput _ (fun value : (input.restrict predicate).Value =>
    ⟨value.val, value.property.1⟩) (fun _ => rfl)

def Implementation.restrictOutput (body : Implementation cost input output f)
    (predicate : B → Prop) [DecidablePred predicate]
    (preserves : ∀ value, input.valid value → predicate (f value)) :
    Implementation cost input (output.restrict predicate) f where
  preserves value valid := ⟨body.preserves value valid, preserves value valid⟩
  program := body.program.viewOutput _ _ (fun _ => rfl)

theorem Implementation.BoundedBy.restrictInput {body : Implementation cost input output f} {time words : Nat}
    (bound : body.BoundedBy time words) (predicate : A → Prop) [DecidablePred predicate] :
    (body.restrictInput predicate).BoundedBy time words :=
  ⟨fun value => bound.time_le ⟨value.val, value.property.1⟩, bound.code_le⟩

theorem Implementation.BoundedBy.restrictOutput {body : Implementation cost input output f} {time words : Nat}
    (bound : body.BoundedBy time words) (predicate : B → Prop) [DecidablePred predicate]
    (preserves : ∀ value, input.valid value → predicate (f value)) :
    (body.restrictOutput predicate preserves).BoundedBy time words := ⟨bound.time_le, bound.code_le⟩

end BoundedSource
end Signatures.Runtime.CaliperBackend
