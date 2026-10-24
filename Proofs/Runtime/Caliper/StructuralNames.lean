import Proofs.Runtime.Caliper.NameBounds
import Proofs.Runtime.Caliper.ExpressionBudget

/-! Name accounting for the source compiler's structural operations. Bounds
survive subtype views because those views retain exactly the same Caliper code. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper Assembly

variable {w : Nat}

theorem Reorder.names (first second third slots : Nat) :
    NamesAccounted (Assembly.code (Reorder.operands (w := w) first second third)) slots := by
  apply Assembly.code_namesAccounted
  simp only [Reorder.operands, Assembly.sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩

theorem ListFold.prepare_names (entry state env capacity slots : Nat) :
    NamesAccounted (ListFold.prepare (w := w) entry state env capacity) slots := by
  apply NamesAccounted.seq
  · apply Assembly.code_namesAccounted
    simp only [ListFold.prepareOperands, Assembly.sourcesBound_append]
    exact ⟨⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
      sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
      sourcesBound_reads _ _ _ _ (by decide)⟩
  · exact CellArithmetic.names _ _ _ _

theorem ListFold.names {body : Stmt w} {slots : Nat} (bound : NamesAccounted body slots)
    (entry state env capacity : Nat) :
    NamesAccounted (ListFold.code body (max 2 body.memBound) entry state env capacity) slots := by
  induction capacity with
  | zero => exact selectSlice_names _ _ _
  | succ capacity ih =>
    exact (loadTag_names slots).seq (NamesAccounted.ifNZ
      ((ListFold.prepare_names _ _ _ _ _).seq
        ((Retain.names bound _ _ _).seq ((Reorder.names _ _ _ _).seq ih)))
      (selectSlice_names _ _ _))

theorem FoldStep.names {body following stop : Stmt w} {slots : Nat}
    (bodyBound : NamesAccounted body slots) (followingBound : NamesAccounted following slots)
    (stopBound : NamesAccounted stop slots) (entry state next env capacity : Nat) :
    NamesAccounted (FoldStep.code body following stop (max 2 body.memBound) entry state next env capacity) slots :=
  (loadTag_names slots).seq (NamesAccounted.ifNZ
    ((ListFold.prepare_names _ _ _ _ _).seq
      ((Retain.names bodyBound _ _ _).seq ((Reorder.names _ _ _ _).seq followingBound)))
    ((selectSlice_names _ _ _).seq stopBound))

theorem Dispatch.names {left right : Stmt w} {slots : Nat}
    (leftBound : NamesAccounted left slots) (rightBound : NamesAccounted right slots)
    (leftWords rightWords : Nat) : NamesAccounted (Dispatch.code left right leftWords rightWords) slots :=
  (loadTag_names slots).seq (NamesAccounted.ifNZ
    ((selectSlice_names _ _ _).seq rightBound) ((selectSlice_names _ _ _).seq leftBound))

variable {A B D : Type} {cost : CostModel}

theorem Pairing.names {input : Representation w A} {left : Representation w B}
    {right : Representation w D} {f : A → B} {g : A → D}
    (first : Realizer cost input left f) (second : Realizer cost input right g)
    (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w)
    (firstNameFits : first.savedBuffer < 2 ^ w) (secondNameFits : second.savedBuffer < 2 ^ w)
    (duplicateFits : input.encoding.words + input.encoding.words < 2 ^ w)
    (middleFits : left.encoding.words + input.encoding.words < 2 ^ w)
    (outputFits : left.encoding.words + right.encoding.words < 2 ^ w)
    {slots : Nat} (firstBound : NamesAccounted first.code slots) (secondBound : NamesAccounted second.code slots) :
    NamesAccounted (Pairing.realizer first second allocation hw firstNameFits secondNameFits duplicateFits middleFits outputFits).code slots := by
  have duplicate := Assembly.code_namesAccounted
    (reads (w := w) 0 0 input.encoding.words ++ reads 0 0 input.encoding.words) slots
    ((sourcesBound_append _ _ _).mpr ⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩)
  exact (((duplicate.seq (Retain.names firstBound _ _ _)).seq (Reorder.names _ _ _ _)).seq
    (Retain.names secondBound _ _ _)).seq (Reorder.names _ _ _ _)

namespace BoundedSource

theorem Implementation.first_names (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) (slots : Nat) :
    NamesAccounted (Implementation.first (cost := .unit) (by decide) left right hw fits).program.code slots :=
  selectSlice_names _ _ _

theorem Implementation.second_names (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) (slots : Nat) :
    NamesAccounted (Implementation.second (cost := .unit) (by decide) left right hw fits).program.code slots :=
  selectSlice_names _ _ _

theorem Implementation.checkedPair_names {input : Layout w A} {left : Layout w B} {right : Layout w D}
    {f : A → B} {g : A → D} (first : Implementation .unit input left f) (second : Implementation .unit input right g)
    (hw : 16 < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w)
    {slots : Nat} (firstBound : NamesAccounted first.program.code slots) (secondBound : NamesAccounted second.program.code slots)
    (implementation : Implementation .unit input (left.prod right outputFits) (fun value => (f value, g value)))
    (compiled : first.checkedPair second (by decide) hw duplicateFits middleFits outputFits = some implementation) :
    NamesAccounted implementation.program.code slots := by
  unfold Implementation.checkedPair at compiled
  split at compiled
  next firstFits =>
    split at compiled
    next secondFits =>
      cases Option.some.inj compiled
      exact Pairing.names first.program second.program (by decide) hw firstFits secondFits
        duplicateFits middleFits outputFits firstBound secondBound
    next rejected => contradiction
  next rejected => contradiction

theorem DataImplementation.unit_names (input : Layout w A) (hw : 16 < 2 ^ w) (slots : Nat) :
    NamesAccounted (DataImplementation.unit .unit (by decide) input hw).program.code slots :=
  Assembly.code_namesAccounted [] slots (sourcesBound_nil _)

theorem DataImplementation.boolean_names (input : Layout w A) (value : Bool) (hw : 16 < 2 ^ w) (slots : Nat) :
    NamesAccounted (DataImplementation.boolean .unit (by decide) input value hw).program.code slots :=
  Assembly.code_namesAccounted _ slots (by simp)

theorem Natural.constant_names (input : Layout w A) (bound value : Nat) (hw : 16 < 2 ^ w)
    (fits : bound ≤ 2 ^ w) (valid : value < bound) (slots : Nat) :
    NamesAccounted (Natural.constant .unit (by decide) input bound value hw fits valid).program.code slots :=
  Assembly.code_namesAccounted _ slots (by simp)

theorem ListData.empty_names (input : Layout w B) (entry : Layout w A) (capacity : Nat)
    (hw : 16 < 2 ^ w) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.representation.encoding.words < 2 ^ w) (slots : Nat) :
    NamesAccounted (ListData.empty .unit (by decide) input entry capacity hw countFits storageFits).program.code slots :=
  Assembly.code_namesAccounted _ slots (sourcesBound_replicate _ _ _)

theorem ListData.cons_names (entry : Layout w A) (capacity : Nat) (hw : 16 < 2 ^ w)
    (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.representation.encoding.words < 2 ^ w) (slots : Nat) :
    NamesAccounted (ListData.cons .unit (by decide) entry capacity hw countFits storageFits).program.code slots := by
  apply NamesAccounted.seq
  · apply Assembly.code_namesAccounted
    simp only [ListConstruct.consOperands, sourcesBound_append]
    exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
      sourcesBound_reads _ _ _ _ (by decide)⟩
  · exact CellArithmetic.names _ _ _ _

theorem ListData.widen_names (entry : Layout w A) (source target : Nat) (increasing : source ≤ target)
    (hw : 16 < 2 ^ w) (countFits : target < 2 ^ w)
    (storageFits : 1 + target * entry.representation.encoding.words < 2 ^ w) (slots : Nat) :
    NamesAccounted (ListData.widen .unit (by decide) entry source target increasing hw countFits storageFits).program.code slots := by
  apply Assembly.code_namesAccounted
  exact (sourcesBound_append _ _ _).mpr ⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_replicate _ _ _⟩

theorem Implementation.checkedBranch_names {input : Layout w A} {output : Layout w B} {hw : 16 < 2 ^ w}
    {condition : A → Bool} {yes no : A → B}
    (test : Implementation .unit input (DataImplementation.boolLayout w (width_pos hw)) condition)
    (left : Implementation .unit input output yes) (right : Implementation .unit input output no)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (tagFits : 1 + input.representation.encoding.words < 2 ^ w)
    {slots : Nat} (testBound : NamesAccounted test.program.code slots)
    (leftBound : NamesAccounted left.program.code slots) (rightBound : NamesAccounted right.program.code slots)
    (implementation : Implementation .unit input output (fun value => if condition value = true then yes value else no value))
    (compiled : test.checkedBranch (hw := hw) left right (by decide) duplicateFits tagFits = some implementation) :
    NamesAccounted implementation.program.code slots := by
  dsimp only [Implementation.checkedBranch] at compiled
  erw [Option.bind_eq_some_iff] at compiled
  obtain ⟨frame, frameEq, compiled⟩ := compiled
  cases Option.some.inj compiled
  have paired := Implementation.checkedPair_names test (Implementation.identity input (width_pos hw)) hw
    duplicateFits tagFits tagFits testBound (skip_names slots) frame frameEq
  exact (paired.seq (CellArithmetic.names _ _ _ _)).seq (Dispatch.names leftBound rightBound _ _)

theorem FoldImplementation.compile_names (entry : Layout w A) (state : Layout w B) (env : Layout w D)
    (argFits : entry.representation.encoding.words + state.representation.encoding.words + env.representation.encoding.words < 2 ^ w)
    {f : A × (B × D) → B} (body : Implementation .unit (FoldImplementation.bodyInput entry state env argFits) state f)
    (hw : 16 < 2 ^ w) (nameFits : body.program.savedBuffer < 2 ^ w) (capacity : Nat) (countFits : capacity < 2 ^ w)
    (fits : 1 + capacity * entry.representation.encoding.words + state.representation.encoding.words + 2 * env.representation.encoding.words < 2 ^ w)
    {slots : Nat} (bound : NamesAccounted body.program.code slots) :
    NamesAccounted (FoldImplementation.compile entry state env argFits body (by decide) hw nameFits capacity countFits fits).program.code slots :=
  ListFold.names bound _ _ _ _

end BoundedSource
end Signatures.Runtime.CaliperBackend
