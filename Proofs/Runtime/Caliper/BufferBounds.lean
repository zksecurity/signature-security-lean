import Proofs.Runtime.Caliper.StructuralNames

/-! Scratch-buffer bounds independent of copied widths and traversal capacity.
These bounds justify the compiler's generated-name checks. They complement the
complete memory account; a small number of buffers does not make copying free. -/

namespace Signatures.Runtime.CaliperBackend

open Caliper Assembly BoundedSource

variable {w : Nat}

theorem selectSlice_buffers (start count : Nat) :
    (selectSlice (w := w) start count).memBound ≤ 2 := by
  have first := (copySlice_names (w := w) 0 1 start count).2
  have second := (copySlice_names (w := w) 1 0 0 count).2
  simp only [selectSlice, Stmt.memBound]
  omega

theorem CellArithmetic.buffers (offset : Nat) (op : BinOp) (operand : Word w) :
    (CellArithmetic.code offset op operand).memBound ≤ 1 := by
  simp [CellArithmetic.code, Stmt.memBound]

theorem Reorder.buffers (first second third : Nat) :
    (Assembly.code (Reorder.operands (w := w) first second third)).memBound ≤ 2 := by
  apply (Assembly.code_names _ 1 ?_).2
  simp only [Reorder.operands, sourcesBound_append]
  exact ⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
    sourcesBound_reads _ _ _ _ (by decide)⟩

theorem ListFold.prepare_buffers (entry state env capacity : Nat) :
    (ListFold.prepare (w := w) entry state env capacity).memBound ≤ 2 := by
  have assembled : (Assembly.code (ListFold.prepareOperands (w := w) entry state env capacity)).memBound ≤ 2 := by
    apply (Assembly.code_names _ 1 ?_).2
    simp only [ListFold.prepareOperands, sourcesBound_append]
    exact ⟨⟨⟨⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩,
      sourcesBound_reads _ _ _ _ (by decide)⟩, sourcesBound_reads _ _ _ _ (by decide)⟩,
      sourcesBound_reads _ _ _ _ (by decide)⟩
  have arithmetic := CellArithmetic.buffers (w := w) (entry + state + env) .sub 1
  simpa only [ListFold.prepare, Stmt.memBound] using max_le assembled (arithmetic.trans (by decide))

theorem ListFold.buffers (body : Stmt w) (entry state env capacity : Nat) :
    (ListFold.code body (max 2 body.memBound) entry state env capacity).memBound ≤ max 2 body.memBound + 1 := by
  induction capacity with
  | zero => exact (selectSlice_buffers _ _).trans (by omega)
  | succ capacity ih =>
    have prepared := ListFold.prepare_buffers (w := w) entry state env capacity
    have retained := (Retain.code_names body (max 2 body.memBound)
      (entry + (state + env)) state (1 + capacity * entry + env)
      (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
    have reordered := Reorder.buffers (w := w) state (1 + capacity * entry) env
    have finished := selectSlice_buffers (w := w) (1 + (capacity + 1) * entry) state
    simp only [ListFold.code, Stmt.memBound]
    omega

theorem Dispatch.buffers (left right : Stmt w) (leftWords rightWords : Nat) :
    (Dispatch.code left right leftWords rightWords).memBound ≤ max 2 (max left.memBound right.memBound) := by
  have first := selectSlice_buffers (w := w) 1 leftWords
  have second := selectSlice_buffers (w := w) 1 rightWords
  simp only [Dispatch.code, Stmt.memBound]
  omega

variable {A B D : Type} {cost : CostModel}

theorem Pairing.buffers {input : Representation w A} {left : Representation w B}
    {right : Representation w D} {f : A → B} {g : A → D}
    (first : Realizer cost input left f) (second : Realizer cost input right g)
    (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w)
    (firstNameFits : first.savedBuffer < 2 ^ w) (secondNameFits : second.savedBuffer < 2 ^ w)
    (duplicateFits : input.encoding.words + input.encoding.words < 2 ^ w)
    (middleFits : left.encoding.words + input.encoding.words < 2 ^ w)
    (outputFits : left.encoding.words + right.encoding.words < 2 ^ w) :
    (Pairing.realizer first second allocation hw firstNameFits secondNameFits duplicateFits middleFits outputFits).code.memBound ≤
      max 2 (max first.code.memBound second.code.memBound) + 1 := by
  have duplicate := (Assembly.code_names
    (reads (w := w) 0 0 input.encoding.words ++ reads 0 0 input.encoding.words) 1
    ((sourcesBound_append _ _ _).mpr ⟨sourcesBound_reads _ _ _ _ (by decide), sourcesBound_reads _ _ _ _ (by decide)⟩)).2
  have one := (Retain.code_names first.code (max 2 first.code.memBound)
    input.encoding.words left.encoding.words input.encoding.words
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  have two := Reorder.buffers (w := w) left.encoding.words input.encoding.words 0
  have three := (Retain.code_names second.code (max 2 second.code.memBound)
    input.encoding.words right.encoding.words left.encoding.words
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)).2
  have four := Reorder.buffers (w := w) right.encoding.words left.encoding.words 0
  change (duplicateRealizer cost allocation input hw duplicateFits).code.memBound ≤ 2 at duplicate
  change (first.retain allocation input hw firstNameFits duplicateFits middleFits).code.memBound ≤ _ at one
  change (Pairing.swap cost allocation left input hw middleFits).code.memBound ≤ 2 at two
  change (second.retain allocation left hw secondNameFits (by omega) (by omega)).code.memBound ≤ _ at three
  change (Pairing.swap cost allocation right left hw (by omega)).code.memBound ≤ 2 at four
  change (max (max (max (max _ _) _) _) _) ≤ _
  omega

namespace BoundedSource

theorem Implementation.first_buffers (allocation : 1 ≤ cost.allocPerWord)
    (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    (Implementation.first allocation left right hw fits).program.code.memBound ≤ 2 :=
  selectSlice_buffers _ _

theorem Implementation.second_buffers (allocation : 1 ≤ cost.allocPerWord)
    (left : Layout w A) (right : Layout w B) (hw : 16 < 2 ^ w)
    (fits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    (Implementation.second allocation left right hw fits).program.code.memBound ≤ 2 :=
  selectSlice_buffers _ _

theorem DataImplementation.boolean_buffers (allocation : 1 ≤ cost.allocPerWord)
    (input : Layout w A) (value : Bool) (hw : 16 < 2 ^ w) :
    (DataImplementation.boolean cost allocation input value hw).program.code.memBound ≤ 2 :=
  (Assembly.code_names _ 1 (by simp [Assembly.SourcesBound, Assembly.Operand.SourcesBound])).2

theorem Implementation.checkedPair_accept {input : Layout w A} {left : Layout w B} {right : Layout w D}
    {f : A → B} {g : A → D} (first : Implementation cost input left f) (second : Implementation cost input right g)
    (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w)
    {firstBuffers secondBuffers : Nat}
    (firstBound : first.program.code.memBound ≤ firstBuffers) (secondBound : second.program.code.memBound ≤ secondBuffers)
    (firstFits : firstBuffers < 2 ^ w) (secondFits : secondBuffers < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (middleFits : left.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (outputFits : left.representation.encoding.words + right.representation.encoding.words < 2 ^ w) :
    ∃ implementation, first.checkedPair second allocation hw duplicateFits middleFits outputFits = some implementation ∧
      implementation.program.code.memBound ≤ max 2 (max firstBuffers secondBuffers) + 1 := by
  have firstName : first.program.savedBuffer < 2 ^ w := by dsimp [Realizer.savedBuffer]; omega
  have secondName : second.program.savedBuffer < 2 ^ w := by dsimp [Realizer.savedBuffer]; omega
  refine ⟨first.pair second allocation hw firstName secondName duplicateFits middleFits outputFits,
    by simp only [Implementation.checkedPair, dite_eq_left firstName, dite_eq_left secondName], ?_⟩
  exact (Pairing.buffers first.program second.program allocation hw firstName secondName
    duplicateFits middleFits outputFits).trans (by omega)

end BoundedSource
end Signatures.Runtime.CaliperBackend
