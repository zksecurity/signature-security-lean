import Proofs.Runtime.Caliper.BufferBounds

/-! Successful checked composition from bounds on generated scratch names. -/

namespace Signatures.Runtime.CaliperBackend.BoundedSource

open Caliper

variable {w : Nat} {A B : Type} {cost : CostModel}

theorem Implementation.checkedBranch_accept {input : Layout w A} {output : Layout w B}
    {hw : 16 < 2 ^ w}
    {condition : A → Bool} {yes no : A → B}
    (test : Implementation cost input (DataImplementation.boolLayout w (width_pos hw)) condition)
    (left : Implementation cost input output yes) (right : Implementation cost input output no)
    (allocation : 1 ≤ cost.allocPerWord)
    {testBuffers leftBuffers rightBuffers : Nat}
    (testBound : test.program.code.memBound ≤ testBuffers)
    (leftBound : left.program.code.memBound ≤ leftBuffers)
    (rightBound : right.program.code.memBound ≤ rightBuffers)
    (testFits : testBuffers < 2 ^ w)
    (duplicateFits : input.representation.encoding.words + input.representation.encoding.words < 2 ^ w)
    (tagFits : 1 + input.representation.encoding.words < 2 ^ w) :
    ∃ implementation, test.checkedBranch (hw := hw) left right allocation duplicateFits tagFits = some implementation ∧
      implementation.program.code.memBound ≤ max (max 2 testBuffers + 1) (max leftBuffers rightBuffers) := by
  obtain ⟨frame, frameEq, frameBound⟩ := test.checkedPair_accept
    (Implementation.identity input (width_pos hw)) allocation hw testBound (show (0 : Nat) ≤ 0 from le_rfl)
    testFits (by omega) duplicateFits tagFits tagFits
  let selected := frame.then (DataImplementation.select cost input hw tagFits)
  let dispatched := selected.then (left.branch right allocation hw (by simpa using tagFits))
  let implementation := dispatched.castFunction (g := fun value => if condition value = true then yes value else no value) (by
    funext value
    cases h : condition value <;> simp [Function.comp_apply, Boolean.select, h])
  refine ⟨implementation, ?_, ?_⟩
  · simp only [Implementation.checkedBranch, frameEq]
    rfl
  · have selected := CellArithmetic.buffers (w := w) 0 .eq 0
    have dispatched := Dispatch.buffers left.program.code right.program.code
      input.representation.encoding.words input.representation.encoding.words
    change max (max frame.program.code.memBound (CellArithmetic.code (w := w) 0 .eq 0).memBound)
      (Dispatch.code left.program.code right.program.code input.representation.encoding.words
        input.representation.encoding.words).memBound ≤ _
    omega

end Signatures.Runtime.CaliperBackend.BoundedSource

namespace Signatures.Runtime.CaliperBackend.SourceExpression

open Caliper BoundedSource

variable {w : Nat} {Atom : Type} {base : Atom → Type} {cost : CostModel}

theorem Variable.buffers {Γ : List (Ty Atom)} {a : Ty Atom} {v : Var Γ a}
    {input : Layout w (Env base Γ)} {output : Layout w (a.Value base)}
    (access : Variable v input output) (allocation : 1 ≤ cost.allocPerWord) (hw : 16 < 2 ^ w) :
    (access.compile allocation hw).program.code.memBound ≤ 2 := by
  induction access with
  | here head tail fits => exact Implementation.first_buffers allocation head tail hw fits
  | there head rest fits ih =>
    exact max_le (Implementation.second_buffers allocation head _ hw fits) ih

end Signatures.Runtime.CaliperBackend.SourceExpression
