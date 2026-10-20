import Signatures.Runtime.Caliper.ListReverseBounds
import Signatures.Runtime.Caliper.CompositionAcceptance
import Signatures.Runtime.Caliper.ImplementationMemory

/-! Compositional construction of local code together with its derived resource
account. These constructors reuse the existing Caliper implementations and
proofs; they introduce neither an interpreter nor a new execution assumption. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource
open Caliper

structure Constructed {w : Nat} {A B : Type} (input : Layout w A) (output : Layout w B) (f : A → B) where
  implementation : Implementation .unit input output f
  budget : Budget
  bounded : implementation.BoundedBy budget.time budget.words
  buffers : Nat
  buffers_le : implementation.program.code.memBound ≤ buffers
  names : ∀ slots, NamesAccounted implementation.program.code slots

namespace Constructed
variable {w : Nat} {A B D : Type} {input : Layout w A} {middle : Layout w B} {output : Layout w D}
    {f : A → B} {g : B → D}

def «then» (first : Constructed input middle f) (second : Constructed middle output g) :
    Constructed input output (g ∘ f) where
  implementation := first.implementation.then second.implementation
  budget := first.budget.seq second.budget
  bounded := first.bounded.then second.bounded
  buffers := max first.buffers second.buffers
  buffers_le := max_le_max first.buffers_le second.buffers_le
  names slots := (first.names slots).seq (second.names slots)

def castFunction {h : A → B} (body : Constructed input middle f) (equal : f = h) :
    Constructed input middle h where
  implementation := body.implementation.castFunction equal
  budget := body.budget
  bounded := body.bounded.castFunction equal
  buffers := body.buffers
  buffers_le := body.buffers_le
  names := body.names

def identity (input : Layout w A) (hw : 0 < w) : Constructed input input id where
  implementation := Implementation.identity input hw
  budget := .identity
  bounded := Implementation.identity_boundedBy input hw
  buffers := 0
  buffers_le := le_rfl
  names := skip_names

def first (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    Constructed (left.prod right fits) left Prod.fst where
  implementation := Implementation.first (by decide) left right hw fits
  budget := .storage left.representation.encoding.words
  bounded := Implementation.first_boundedBy left right hw fits
  buffers := 2
  buffers_le := Implementation.first_buffers _ _ _ _ _
  names := Implementation.first_names left right hw fits

def second (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    Constructed (left.prod right fits) right Prod.snd where
  implementation := Implementation.second (by decide) left right hw fits
  budget := .storage right.representation.encoding.words
  bounded := Implementation.second_boundedBy left right hw fits
  buffers := 2
  buffers_le := Implementation.second_buffers _ _ _ _ _
  names := Implementation.second_names left right hw fits

def constant (input : Layout w A) (output : Layout w B) (value : output.Value) (hw : 16 < 2 ^ w) :
    Constructed input output (fun _ => value.val) where
  implementation := Implementation.constant input output value hw
  budget := .storage output.representation.encoding.words
  bounded := Implementation.constant_bounded input output value hw
  buffers := 2
  buffers_le := Implementation.constant_buffers input output value hw
  names := Implementation.constant_names input output value hw

theorem nameFits (body : Constructed input middle f) (hw : 16 < 2 ^ w) (room : body.buffers < 2 ^ w) :
    body.implementation.program.savedBuffer < 2 ^ w := by
  have := body.buffers_le
  dsimp only [Realizer.savedBuffer]
  omega

def pair {left : Layout w B} {right : Layout w D} {f : A → B} {g : A → D}
    (first : Constructed input left f) (second : Constructed input right g) (hw : 16 < 2 ^ w)
    (firstFits : first.buffers < 2 ^ w) (secondFits : second.buffers < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    Constructed input (left.prod right outputFits) (fun value => (f value, g value)) where
  implementation := first.implementation.pair second.implementation (by decide) hw
    (first.nameFits hw firstFits) (second.nameFits hw secondFits) duplicateFits middleFits outputFits
  budget := .pair input.representation.encoding.words left.representation.encoding.words right.representation.encoding.words
    first.budget second.budget
  bounded := Implementation.pair_boundedBy _ _ _ _ _ _ _ _ first.bounded second.bounded
  buffers := max 2 (max first.buffers second.buffers) + 1
  buffers_le := Implementation.pair_buffers _ _ _ _ _ _ _ _ first.buffers_le second.buffers_le
  names slots := Implementation.pair_names _ _ _ _ _ _ _ _ (first.names slots) (second.names slots)

def branch {output : Layout w B} {condition : A → Bool} {yes no : A → B}
    (hw : 16 < 2 ^ w) (test : Constructed input (DataImplementation.boolLayout w (width_pos hw)) condition)
    (left : Constructed input output yes) (right : Constructed input output no)
    (testFits : test.buffers < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (tagFits : 1 + input.representation.encoding.words < 2 ^ w) :
    Constructed input output (fun value => if condition value = true then yes value else no value) :=
  let compiled := test.implementation.checkedBranch (hw := hw) left.implementation right.implementation
    (by decide) duplicateFits tagFits
  let accepted := Implementation.checkedBranch_accept test.implementation left.implementation right.implementation
    (by decide) test.buffers_le left.buffers_le right.buffers_le testFits duplicateFits tagFits
  have present : compiled.isSome := by obtain ⟨result, equal, _⟩ := accepted; dsimp only [compiled]; rw [equal]; rfl
  let result := compiled.get present
  have equal : compiled = some result := Option.eq_some_of_isSome present
  { implementation := result
    budget := .branch input.representation.encoding.words test.budget left.budget right.budget
    bounded := Implementation.checkedBranch_boundedBy _ _ _ duplicateFits tagFits _ _ _ _ _ _
      test.bounded left.bounded right.bounded result equal
    buffers := max (max 2 test.buffers + 1) (max left.buffers right.buffers)
    buffers_le := by
      obtain ⟨body, got, bounded⟩ := accepted
      rw [Option.some.inj (equal.symm.trans got)]
      exact bounded
    names := fun slots => Implementation.checkedBranch_names _ _ _ duplicateFits tagFits
      (test.names slots) (left.names slots) (right.names slots) result equal }

def equal (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    Constructed (Natural.pair left right hw leftFits rightFits) (DataImplementation.boolLayout w (width_pos hw))
      (fun value => decide (value.1 = value.2)) where
  implementation := Natural.equal .unit left right hw leftFits rightFits
  budget := ⟨6, 27⟩
  bounded := ⟨fun _ => le_rfl, (WordBinary.descriptionWords_eq .eq).le⟩
  buffers := 1
  buffers_le := le_rfl
  names slots := ⟨by change 3 ≤ slots + 27; omega, by change 1 ≤ slots + 27; omega⟩

def cons (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.representation.encoding.words < 2 ^ w) :
    Constructed (ListData.consInput entry capacity hw countFits storageFits)
      (entry.boundedList (capacity + 1) countFits storageFits) (fun value => value.1 :: value.2) where
  implementation := ListData.cons .unit (by decide) entry capacity hw countFits storageFits
  budget := .cons (1 + (capacity + 1) * entry.representation.encoding.words)
  bounded := ListData.cons_boundedBy entry capacity hw countFits storageFits
  buffers := 2
  buffers_le := max_le
    ((Assembly.code_names (ListConstruct.consOperands (w := w) entry.representation.encoding.words capacity) 1 (by
      simp only [ListConstruct.consOperands, Assembly.sourcesBound_append]
      exact ⟨⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩,
        Assembly.sourcesBound_reads _ _ _ _ (by decide)⟩)).2)
    ((CellArithmetic.buffers (w := w) 0 .add 1).trans (by decide))
  names := ListData.cons_names entry capacity hw countFits storageFits

def widen (entry : Layout w A) (source target : Nat) (increasing : source ≤ target) (hw : 16 < 2 ^ w)
    (countFits : target < 2 ^ w) (storageFits : 1 + target * entry.representation.encoding.words < 2 ^ w) :
    Constructed (entry.boundedList source (increasing.trans_lt countFits) (by nlinarith))
      (entry.boundedList target countFits storageFits) id where
  implementation := ListData.widen .unit (by decide) entry source target increasing hw countFits storageFits
  budget := .storage (1 + target * entry.representation.encoding.words)
  bounded := ListData.widen_boundedBy entry source target increasing hw countFits storageFits
  buffers := 2
  buffers_le := (Assembly.code_names _ 1 ((Assembly.sourcesBound_append _ _ _).mpr
    ⟨Assembly.sourcesBound_reads _ _ _ _ (by decide), Assembly.sourcesBound_replicate _ _ _⟩)).2
  names := ListData.widen_names entry source target increasing hw countFits storageFits

def reverse (layout : ListReverse.Layouts w A) : Constructed layout.list layout.list List.reverse where
  implementation := ListReverse.implementation layout
  budget := ⟨ListReverse.timeBudget layout, ListReverse.codeBudget layout⟩
  bounded := ListReverse.bounded layout
  buffers := 3
  buffers_le := ListReverse.buffers layout
  names := ListReverse.names layout

end Constructed
end Signatures.Runtime.CaliperBackend.BoundedSource
