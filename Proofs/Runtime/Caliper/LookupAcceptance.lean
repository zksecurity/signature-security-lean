import Proofs.Runtime.Caliper.LookupExpression
import Proofs.Runtime.Caliper.FoldEmission

/-! Every encoded lookup layout satisfying its stated width/capacity conditions
compiles successfully. The proof follows the original certificate and shows
that at most seven buffer names are needed, independently of table capacity.
The resulting total implementation retains the existing execution budgets. -/

namespace Signatures.Runtime.CaliperBackend.SourceLookup

open Caliper BoundedSource SourceExpression

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    (P : Primitives base Op) {key val : Ty Atom}
    (layout : LookupLayout w (key.Value base) (val.Value base))

theorem entry_emits : (entryCode P layout).Emits 2 := Compilation.Emits.var _
theorem accumulator_emits : (accumulatorCode P layout).Emits 2 := Compilation.Emits.var _
theorem key_emits : (keyCode P layout).Emits 2 := Compilation.Emits.var _
theorem default_emits : (defaultCode P layout).Emits 2 := Compilation.Emits.var _
theorem table_emits : (tableCode P layout).Emits 2 := Compilation.Emits.var _

theorem found_emits : (foundCode P layout).Emits 3 := by
  have hw := layout.wordFits
  unfold foundCode
  apply Compilation.Emits.pair (firstBuffers := 2) (secondBuffers := 2)
  · exact Compilation.Emits.bool _ _
  · exact Compilation.Emits.snd _ _ _ (entry_emits P layout)
  · omega
  · omega

theorem initial_emits : (initialCode P layout).Emits 3 := by
  have hw := layout.wordFits
  unfold initialCode
  apply Compilation.Emits.pair (firstBuffers := 2) (secondBuffers := 2)
  · exact Compilation.Emits.bool _ _
  · exact default_emits P layout
  · omega
  · omega

variable (eq : Op (.pair key key) .bool)
    (comparison : Implementation .unit (layout.key.prod layout.key layout.keyPairFits) layout.boolean (P.execute eq))
    (comparisonBuffers : comparison.program.code.memBound ≤ 5)

include comparisonBuffers

theorem test_emits : (testCode P eq layout comparison).Emits 5 := by
  have hw := layout.wordFits
  unfold testCode
  apply Compilation.Emits.op (buffers := 3) (primitiveBuffers := 5)
  · apply Compilation.Emits.pair (firstBuffers := 2) (secondBuffers := 2)
    · exact Compilation.Emits.fst _ _ _ (entry_emits P layout)
    · exact key_emits P layout
    · omega
    · omega
  · exact comparisonBuffers

theorem body_emits : (bodyCode P eq layout comparison).Emits 6 := by
  have hw := layout.wordFits
  unfold bodyCode
  apply Compilation.Emits.branch (testBuffers := 2) (leftBuffers := 2) (rightBuffers := 6)
  · exact Compilation.Emits.fst _ _ _ (accumulator_emits P layout)
  · exact accumulator_emits P layout
  · apply Compilation.Emits.branch (testBuffers := 5) (leftBuffers := 3) (rightBuffers := 2)
    · exact test_emits P layout eq comparison comparisonBuffers
    · exact found_emits P layout
    · exact accumulator_emits P layout
    · omega
  · omega

theorem emits : (certificate P eq layout comparison).Emits 7 := by
  have hw := layout.wordFits
  unfold certificate
  exact Compilation.Emits.fold (P := P) (Γ := Context key val) (a := .pair key val) (b := .pair .bool val)
    layout.input layout.entry layout.result layout.capacity layout.countFits
    layout.argumentFits layout.frameFits (table_emits P layout) (initial_emits P layout)
    (body_emits P layout eq comparison comparisonBuffers) (by omega) (by omega) (by omega)

end Signatures.Runtime.CaliperBackend.SourceLookup

namespace Signatures.Runtime.CaliperBackend.EncodedLookup

open Caliper BoundedSource SourceExpression

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key val : Ty Atom}
    [DecidableEq (key.Value base)] (layout : LookupLayout w (key.Value base) (val.Value base))

theorem emits : (certificate layout).Emits 7 :=
  SourceLookup.emits _ _ _ _ (SourceLookup.encodedNames _ _ _ (fun _ _ => rfl)).buffers

variable {Op : Ty Atom → Ty Atom → Type} (P : Primitives base Op)
    (comparison : Expr Op [key, key] .bool)
    (correct : ∀ left right, comparison.denote P (left, right, ()) = decide (left = right))

theorem accepted : (compile layout P comparison correct).isSome := by
  rw [compile_isSome]
  exact (emits layout).isSome

/-- A total implementation on every admitted layout, obtained from the existing
compiler with its acceptance now proved for all parameter values. -/
def implementation : Implementation .unit layout.input layout.result ((lookupExpr comparison).denote P) :=
  (compile layout P comparison correct).get (accepted layout P comparison correct)

theorem compiled : compile layout P comparison correct = some (implementation layout P comparison correct) :=
  Option.eq_some_of_isSome (accepted layout P comparison correct)

theorem implementation_bounded : (implementation layout P comparison correct).BoundedBy (timeBudget layout) (codeBudget layout) :=
  bounded layout P comparison correct _ (compiled layout P comparison correct)

theorem implementation_buffers : (implementation layout P comparison correct).program.code.memBound ≤ 7 := by
  obtain ⟨body, bodyEq, resultEq⟩ := Option.map_eq_some_iff.mp (compiled layout P comparison correct)
  rw [← resultEq]
  exact (emits layout).buffers body bodyEq

end Signatures.Runtime.CaliperBackend.EncodedLookup
