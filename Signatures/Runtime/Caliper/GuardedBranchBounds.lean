import Signatures.Runtime.Caliper.GuardedBranch

/-! The branch-local refinements retain the actual selector and dispatch code.
These bounds charge for testing, retaining/copying the input, storing the tag
and dispatching. Neither the refinement predicate nor its proof executes. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource.GuardedBranch

open Caliper

variable {w : Nat} {A B : Type} {input : Layout w A} {hw : 16 < 2 ^ w}
    {condition : A → Bool}
    (test : Implementation .unit input (DataImplementation.boolLayout w (width_pos hw)) condition)
    (nameFits : test.program.savedBuffer < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (tagFits : 1 + input.representation.encoding.words < 2 ^ w)

theorem selector_boundedBy {time words : Nat} (bound : test.BoundedBy time words) :
    (selector (hw := hw) test (by decide) nameFits duplicateFits tagFits).BoundedBy
      (time + 68 * input.representation.encoding.words + 41)
      (words + 221 * input.representation.encoding.words + 266) := by
  have identityFits : (Implementation.identity (cost := .unit) input (width_pos hw)).program.savedBuffer < 2 ^ w := by
    change max 2 0 < 2 ^ w
    omega
  let paired := test.pair (Implementation.identity input (width_pos hw)) (by decide) hw nameFits identityFits
    duplicateFits tagFits tagFits
  have pairBound := Implementation.checkedPair_boundedBy test (Implementation.identity input (width_pos hw)) hw
    duplicateFits tagFits tagFits time words 0 1 bound (Implementation.identity_boundedBy input (width_pos hw)) paired
    (by simp only [Implementation.checkedPair, dite_eq_left nameFits, dite_eq_left identityFits]; rfl)
  have selected := pairBound.then (DataImplementation.select_boundedBy input hw tagFits)
  constructor
  · intro value
    exact (selected.time_le value).trans (by
      change time + 0 + 52 * input.representation.encoding.words + 36 * 1 + 16 * input.representation.encoding.words + 5 ≤ _
      omega)
  · exact selected.code_le.trans (by
      change words + 1 + 169 * input.representation.encoding.words + 117 * 1 + 52 * input.representation.encoding.words + 124 + 23 + 1 ≤ _
      omega)

theorem selector_buffers {buffers : Nat} (bound : test.program.code.memBound ≤ buffers) :
    (selector (hw := hw) test (by decide) nameFits duplicateFits tagFits).program.code.memBound ≤ max 2 buffers + 1 := by
  have paired := Pairing.buffers test.program (Implementation.identity (cost := .unit) input (width_pos hw)).program
    (by decide) hw nameFits (by change max 2 0 < 2 ^ w; omega) duplicateFits tagFits tagFits
  have selected := CellArithmetic.buffers (w := w) 0 .eq 0
  change max (Pairing.realizer test.program (Implementation.identity (cost := .unit) input (width_pos hw)).program
    (by decide) hw nameFits _ duplicateFits tagFits tagFits).code.memBound
    (CellArithmetic.code (w := w) 0 .eq 0).memBound ≤ _
  change _ ≤ max 2 (max test.program.code.memBound 0) + 1 at paired
  omega

theorem selector_names {slots : Nat} (bound : NamesAccounted test.program.code slots) :
    NamesAccounted (selector (hw := hw) test (by decide) nameFits duplicateFits tagFits).program.code slots := by
  have paired := Pairing.names test.program (Implementation.identity (cost := .unit) input (width_pos hw)).program
    (by decide) hw nameFits (by change max 2 0 < 2 ^ w; omega) duplicateFits tagFits tagFits bound (skip_names slots)
  exact paired.seq (CellArithmetic.names _ _ _ _)

variable {output : Layout w B} {yes no : A → B}
    (left : Implementation .unit (yesInput input condition) output yes)
    (right : Implementation .unit (noInput input condition) output no)

theorem implementation_boundedBy {testTime testWords leftTime leftWords rightTime rightWords : Nat}
    (testBound : test.BoundedBy testTime testWords) (leftBound : left.BoundedBy leftTime leftWords)
    (rightBound : right.BoundedBy rightTime rightWords) :
    (implementation (hw := hw) test (by decide) nameFits duplicateFits tagFits left right).BoundedBy
      (testTime + leftTime + rightTime + 76 * input.representation.encoding.words + 43)
      (testWords + leftWords + rightWords + 273 * input.representation.encoding.words + 304) := by
  have selected := selector_boundedBy (hw := hw) test nameFits duplicateFits tagFits testBound
  have dispatched := selected.then (Implementation.branch_boundedBy left right hw
    (by simpa [yesInput, noInput] using tagFits) _ _ _ _ leftBound rightBound)
  apply (dispatched.castFunction _).mono
  · simp only [yesInput, noInput, Layout.restrict_words, Nat.max_self]
    omega
  · simp only [yesInput, noInput, Layout.restrict_words]
    omega

theorem implementation_buffers {testBuffers leftBuffers rightBuffers : Nat}
    (testBound : test.program.code.memBound ≤ testBuffers)
    (leftBound : left.program.code.memBound ≤ leftBuffers) (rightBound : right.program.code.memBound ≤ rightBuffers) :
    (implementation (hw := hw) test (by decide) nameFits duplicateFits tagFits left right).program.code.memBound ≤
      max (max 2 testBuffers + 1) (max leftBuffers rightBuffers) := by
  have selected := selector_buffers (hw := hw) test nameFits duplicateFits tagFits testBound
  have dispatched := Dispatch.buffers left.program.code right.program.code
    (yesInput input condition).representation.encoding.words (noInput input condition).representation.encoding.words
  change max (selector (hw := hw) test (by decide) nameFits duplicateFits tagFits).program.code.memBound
    (Dispatch.code left.program.code right.program.code
      (yesInput input condition).representation.encoding.words (noInput input condition).representation.encoding.words).memBound ≤ _
  omega

theorem implementation_names {slots : Nat} (testBound : NamesAccounted test.program.code slots)
    (leftBound : NamesAccounted left.program.code slots) (rightBound : NamesAccounted right.program.code slots) :
    NamesAccounted (implementation (hw := hw) test (by decide) nameFits duplicateFits tagFits left right).program.code slots :=
  (selector_names (hw := hw) test nameFits duplicateFits tagFits testBound).seq (Dispatch.names leftBound rightBound _ _)

end Signatures.Runtime.CaliperBackend.BoundedSource.GuardedBranch
