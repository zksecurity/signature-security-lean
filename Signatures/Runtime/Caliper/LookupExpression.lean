import Signatures.Runtime.Caliper.LookupBounds
import Signatures.Runtime.LookupExpr

/-! Verified normalization of structured-key lookup to encoded equality.

The source comparator must be proved to test equality. The generated program
then compares the complete stored key encodings, without interpreting that
source expression or invoking a host callback. The existing lookup compiler
constructs all traversal code and supplies its time, code and name bounds.
This is a semantic compilation rule; it does not claim to preserve source cost.
-/

namespace Signatures.Runtime.CaliperBackend.EncodedLookup

open Caliper BoundedSource SourceExpression

inductive EqualityOp {Atom : Type} (key : Ty Atom) : Ty Atom → Ty Atom → Type
  | equal : EqualityOp key (.pair key key) .bool

def primitives {Atom : Type} (base : Atom → Type) (key : Ty Atom)
    [DecidableEq (key.Value base)] (words : Nat) : Primitives base (EqualityOp key) where
  execute instruction := match instruction with
    | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 6 * words + 3

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] (layout : LookupLayout w (key.Value base) (val.Value base))

def certificate :=
  let P := primitives base key layout.key.representation.encoding.words
  SourceLookup.certificate P (val := val) .equal layout
    (SourceLookup.encodedComparison P .equal layout (fun _ _ => rfl))

def bounds : (certificate layout).LocalBounds :=
  let P := primitives base key layout.key.representation.encoding.words
  SourceLookup.localBounds P (val := val) .equal layout
    (SourceLookup.encodedComparison P .equal layout (fun _ _ => rfl))
    (SourceLookup.encodedBudget P .equal layout (fun _ _ => rfl))

def timeBudget : Nat := SourceLookup.timeBudget layout.key.representation.encoding.words
  layout.value.representation.encoding.words layout.capacity (6 * layout.key.representation.encoding.words + 3)

def codeBudget : Nat := SourceLookup.codeBudget layout.key.representation.encoding.words
  layout.value.representation.encoding.words layout.capacity (30 * layout.key.representation.encoding.words + 13)

theorem budget_time : ((certificate layout).budget (bounds layout)).time = timeBudget layout :=
  SourceLookup.budget_time_eq _ _ _ _ _

theorem budget_words : ((certificate layout).budget (bounds layout)).words = codeBudget layout :=
  SourceLookup.budget_words_eq _ _ _ _ _

theorem primitiveNames : (certificate layout).PrimitiveNames 5 :=
  SourceLookup.primitiveNames _ _ _ _ (SourceLookup.encodedNames _ _ _ (fun _ _ => rfl))

variable {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

include correct in
theorem source_eq :
    (lookup (val := val) (EqualityOp.equal (key := key))).denote
      (primitives base key layout.key.representation.encoding.words) = (lookupExpr comparison).denote P := by
  funext value
  have original := lookupExpr_value P comparison correct value.1 value.2.1 value.2.2.1
  rw [Expr.run_value] at original
  exact (SourceLookup.source_value _ _ (fun _ _ => rfl) value).trans original.symm

/-- Compile the original structured lookup using proved equality of its result
with encoded-key lookup. Failure remains an explicit scratch-name rejection. -/
def compile : Option (Implementation .unit layout.input layout.result ((lookupExpr comparison).denote P)) :=
  (certificate layout).compile (by decide) |>.map
    (fun implementation => implementation.castFunction (source_eq layout P comparison correct))

theorem compile_isSome : (compile layout P comparison correct).isSome =
    ((certificate layout).compile (by decide)).isSome := by simp [compile]

theorem bounded (implementation : Implementation .unit layout.input layout.result ((lookupExpr comparison).denote P))
    (compiled : compile layout P comparison correct = some implementation) :
    implementation.BoundedBy (timeBudget layout) (codeBudget layout) := by
  obtain ⟨body, accepted, rfl⟩ := Option.map_eq_some_iff.mp compiled
  have bound := (certificate layout).bounded (bounds layout) body accepted
  rw [budget_time, budget_words] at bound
  exact bound.castFunction _

theorem names (implementation : Implementation .unit layout.input layout.result ((lookupExpr comparison).denote P))
    (compiled : compile layout P comparison correct = some implementation) :
    NamesBound implementation.program.code (5 + codeBudget layout) := by
  obtain ⟨body, accepted, rfl⟩ := Option.map_eq_some_iff.mp compiled
  have bound := (certificate layout).nameBounds (bounds layout) (primitiveNames layout) body accepted
  rw [budget_words] at bound
  exact bound

theorem staticMemory (implementation : Implementation .unit layout.input layout.result ((lookupExpr comparison).denote P))
    (compiled : compile layout P comparison correct = some implementation) (registers buffers : Nat) :
    staticWords implementation.program.code registers buffers ≤
      5 * codeBudget layout + 20 + registers + 3 * buffers := by
  obtain ⟨body, accepted, rfl⟩ := Option.map_eq_some_iff.mp compiled
  have bound := (certificate layout).staticMemory_bound (bounds layout) (primitiveNames layout) body accepted registers buffers
  apply bound.trans
  have estimate := Budget.staticMemory_le ((certificate layout).budget (bounds layout)) 5 registers buffers
  simpa only [budget_words] using estimate

/-- The normalization also preserves the complete memory account, including
caller-owned initial capacity and every intermediate state of execution. -/
theorem memoryBound (implementation : Implementation .unit layout.input layout.result ((lookupExpr comparison).denote P))
    (compiled : compile layout P comparison correct = some implementation)
    (tape : RandomTape w) (environment : layout.input.Value) (before : State w)
    (represented : layout.input.representation.Holds environment before)
    (registers buffers : Nat) (initialRegisters : RegisterBound before registers)
    (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape implementation.program.code before after
        (implementation.program.time environment) net peak ∧
      layout.result.representation.Holds
        ⟨(lookupExpr comparison).denote P environment.val, implementation.preserves environment.val environment.property⟩ after ∧
      implementation.program.time environment ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape implementation.program.code before between ∨ between = after) →
        RegisterBound between (max registers (registerSlots implementation.program.code)) ∧
        between.SupportBound (max buffers implementation.program.code.memBound) ∧ between.WellFormed ∧
        (staticWords implementation.program.code registers buffers : Int) +
          between.liveMem (max buffers implementation.program.code.memBound) ≤
            5 * codeBudget layout + 20 + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, _, peakBound⟩ :=
    (bounded layout P comparison correct implementation compiled).exec (by decide) tape environment before represented
  refine ⟨after, net, peak, execution, output, elapsed, ?_⟩
  intro between visited
  obtain ⟨registerBound, bufferBound, wellFormed, memory⟩ :=
    LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers represented.2.2.1
  refine ⟨registerBound, bufferBound, wellFormed, ?_⟩
  have staticBound := staticMemory layout P comparison correct implementation compiled registers buffers
  omega

end Signatures.Runtime.CaliperBackend.EncodedLookup
