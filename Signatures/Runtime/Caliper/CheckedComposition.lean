import Signatures.Runtime.Caliper.SourceStructure
import Signatures.Runtime.Caliper.SourceFold

/-! Composition with checked generated scratch names. Failure is a compiler
rejection, not a premise that the executed program may exceed its word width. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper

variable {w : Nat} {A B D : Type} {cost : CostModel}

def Implementation.castFunction {input : Layout w A} {output : Layout w B} {f g : A → B}
    (body : Implementation cost input output f) (equal : f = g) : Implementation cost input output g where
  preserves value valid := by rw [← equal]; exact body.preserves value valid
  program := body.program.viewOutput _ _ (by
    intro value
    apply congrArg output.representation.encoding.encode
    apply Subtype.ext
    exact (congrFun equal value.val).symm)

/-- Change an admitted domain only when the value and its stored bytes agree.
Unlike list capacity growth, this rule cannot add padding or execute a conversion. -/
def Implementation.view {input output : Layout w A} (hw : 0 < w)
    (preserves : ∀ value, input.valid value → output.valid value)
    (sameBytes : ∀ value : input.Value,
      output.representation.encoding.encode ⟨value.val, preserves value.val value.property⟩ =
        input.representation.encoding.encode value) : Implementation cost input output id where
  preserves := preserves
  program := (Realizer.identity hw input.representation).viewOutput _ _ sameBytes

def Implementation.checkedPair {input : Layout w A} {left : Layout w B} {right : Layout w D}
    {f : A → B} {g : A → D} (first : Implementation cost input left f) (second : Implementation cost input right g)
    (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    Option (Implementation cost input (left.prod right outputFits) (fun value => (f value, g value))) :=
  if firstFits : first.program.savedBuffer < 2 ^ w then
    if secondFits : second.program.savedBuffer < 2 ^ w then
      some (first.pair second allocation hw firstFits secondFits duplicateFits middleFits outputFits)
    else none
  else none

def Implementation.checkedBranch {input : Layout w A} {output : Layout w B} {hw : 16 < 2 ^ w}
    {condition : A → Bool} {yes no : A → B}
    (test : Implementation cost input (DataImplementation.boolLayout w (width_pos hw)) condition)
    (left : Implementation cost input output yes) (right : Implementation cost input output no)
    (allocation : 1 ≤ cost.allocPerWord)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (tagFits : 1 + input.representation.encoding.words < 2 ^ w) :
    Option (Implementation cost input output (fun value => if condition value = true then yes value else no value)) := do
  let frame ← test.checkedPair (Implementation.identity input (width_pos hw)) allocation hw duplicateFits tagFits tagFits
  let selected := frame.then (DataImplementation.select cost input hw tagFits)
  let dispatched := selected.then (left.branch right allocation hw (by simpa using tagFits))
  pure (dispatched.castFunction (by
    funext value
    cases h : condition value <;> simp [Function.comp_apply, Boolean.select, h]))

end Signatures.Runtime.CaliperBackend.BoundedSource
