import Signatures.Runtime.Caliper.RestrictedLayout
import Signatures.Runtime.Caliper.BranchBudgets
import Signatures.Runtime.Caliper.CompositionAcceptance

/-! Branch-local input invariants from an executed Boolean test. The selector
runs the test, retains its input and writes the sum tag. Refined domains record
which answer was observed; no host predicate supplies an uncharged decision. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.GuardedBranch

open Caliper

variable {w : Nat} {A B : Type} {cost : CostModel}

def yesInput (input : Layout w A) (condition : A → Bool) : Layout w A :=
  input.restrict (fun value => condition value = true)

def noInput (input : Layout w A) (condition : A → Bool) : Layout w A :=
  input.restrict (fun value => condition value = false)

def select (condition : A → Bool) (value : A) : A ⊕ A :=
  if condition value then .inl value else .inr value

variable {input : Layout w A} {hw : 16 < 2 ^ w} {condition : A → Bool}
    (test : Implementation cost input (DataImplementation.boolLayout w (width_pos hw)) condition)
    (allocation : 1 ≤ cost.allocPerWord)
    (nameFits : test.program.savedBuffer < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (tagFits : 1 + input.representation.encoding.words < 2 ^ w)

def selector : Implementation cost input
    ((yesInput input condition).sum (noInput input condition) (width_pos hw) (by simpa [yesInput, noInput] using tagFits))
    (select condition) where
  preserves value valid := by
    cases h : condition value <;>
      simp [select, h, Layout.sum, yesInput, noInput, Layout.restrict, valid]
  program :=
    let paired := test.pair (Implementation.identity input (width_pos hw)) allocation hw nameFits
      (by change max 2 0 < 2 ^ w; omega) duplicateFits tagFits tagFits
    let selected := paired.then (DataImplementation.select cost input hw tagFits)
    selected.program.viewOutput _ _ (by
      intro value
      change ((yesInput input condition).sum (noInput input condition) (width_pos hw) _).representation.encoding.encode
          ⟨select condition value.val, _⟩ =
        (input.sum input (width_pos hw) _).representation.encoding.encode ⟨Boolean.select (condition value.val, value.val), _⟩
      by_cases h : condition value.val = true <;>
        simp [select, Boolean.select, h, Layout.sum, sumView, yesInput, noInput,
          Layout.restrict, restrictedView, Representation.transport, Encoding.transport,
          Representation.restrict, Encoding.restrict, Representation.sum, Encoding.sum, Encoding.checked] <;> rfl)

def implementation {output : Layout w B} {yes no : A → B}
    (left : Implementation cost (yesInput input condition) output yes)
    (right : Implementation cost (noInput input condition) output no) :
    Implementation cost input output (fun value => if condition value = true then yes value else no value) :=
  ((selector (hw := hw) test allocation nameFits duplicateFits tagFits).then
    (left.branch right allocation hw (by simpa [yesInput, noInput] using tagFits))).castFunction (by
      funext value
      cases h : condition value <;> simp [Function.comp_apply, select, h])

end Signatures.Runtime.CaliperBackend.BoundedSource.GuardedBranch
