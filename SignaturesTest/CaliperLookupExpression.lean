import Signatures.Runtime.Caliper.LookupExpression
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource

namespace SignaturesTest.CaliperLookupExpression

private def base (_ : Unit) : Type := Word 8
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1

private abbrev key : Ty Unit := .pair .nat .nat
private def comparison : Expr Op [key, key] .bool :=
  .branch (.op .equal (.pair (.fst (.var .here)) (.fst (.var (.there .here)))))
    (.op .equal (.pair (.snd (.var .here)) (.snd (.var (.there .here))))) (.bool false)

private theorem comparison_correct (left right : Nat × Nat) :
    comparison.denote primitives (left, right, ()) = decide (left = right) := by
  by_cases h : left.1 = right.1 <;>
    simp [comparison, Expr.denote, Var.get, primitives, h, Prod.ext_iff]
  exact decide_eq_decide.mpr Iff.rfl

private def counter := Layout.counter 8 256 (by decide) (by decide)
private def layout : LookupLayout 8 (Nat × Nat) Nat where
  key := counter.prod counter (by decide)
  value := counter
  capacity := 2
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def compiled := EncodedLookup.compile (base := base) (key := key) (val := .nat) layout primitives comparison comparison_correct
private theorem accepted : compiled.isSome := by decide +kernel
private def program := compiled.get accepted
private theorem compiled_eq : compiled = some program := Option.eq_some_of_isSome accepted

private theorem time_eq : EncodedLookup.timeBudget (base := base) (key := key) (val := .nat) layout = 14813 := by decide +kernel
private theorem code_eq : EncodedLookup.codeBudget (base := base) (key := key) (val := .nat) layout = 53660 := by decide +kernel

private theorem bounded : program.BoundedBy 14813 53660 := by
  rw [← time_eq, ← code_eq]
  exact EncodedLookup.bounded (base := base) (key := key) (val := .nat) layout primitives comparison comparison_correct program
    compiled_eq

example : NamesBound program.program.code 53665 := by
  have bound := EncodedLookup.names (base := base) (key := key) (val := .nat) layout primitives comparison comparison_correct program
    compiled_eq
  rw [code_eq] at bound
  exact bound
example : staticWords program.program.code 5 201 ≤ 268928 := by
  have bound := EncodedLookup.staticMemory (base := base) (key := key) (val := .nat) layout primitives comparison comparison_correct program
    compiled_eq 5 201
  rw [code_eq] at bound
  exact bound

private def observe (value : layout.input.Value) := do
  let initial := layout.input.representation.initial value
  let before := { initial with
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 1 else initial.caps buffer }
  let (state, _, _, _) ← Caliper.run .unit RandomTape.zero 30000 program.program.code before
  pure (state.bufs 0, state.bufs 200)

private def sameFirst : layout.input.Value := ⟨((2, 5), 9, [((2, 4), 7), ((2, 5), 0)], ()), by
  change (2 < 256 ∧ 5 < 256) ∧ 9 < 256 ∧
    (_ ≤ 2 ∧ ∀ p ∈ [((2, 4), 7), ((2, 5), 0)], (p.1.1 < 256 ∧ p.1.2 < 256) ∧ p.2 < 256) ∧ True
  decide⟩
private def sameSecond : layout.input.Value := ⟨((2, 5), 9, [((1, 5), 7), ((2, 5), 8)], ()), by
  change (2 < 256 ∧ 5 < 256) ∧ 9 < 256 ∧
    (_ ≤ 2 ∧ ∀ p ∈ [((1, 5), 7), ((2, 5), 8)], (p.1.1 < 256 ∧ p.1.2 < 256) ∧ p.2 < 256) ∧ True
  decide⟩
private def miss : layout.input.Value := ⟨((2, 5), 9, [((2, 4), 7), ((1, 5), 8)], ()), by
  change (2 < 256 ∧ 5 < 256) ∧ 9 < 256 ∧
    (_ ≤ 2 ∧ ∀ p ∈ [((2, 4), 7), ((1, 5), 8)], (p.1.1 < 256 ∧ p.1.2 < 256) ∧ p.2 < 256) ∧ True
  decide⟩

-- Both key components affect the original source game and the emitted program.
example : observe sameFirst = some (#[1, 0], #[77]) := by decide +kernel
example : observe sameSecond = some (#[1, 8], #[77]) := by decide +kernel
example : observe miss = some (#[0, 9], #[77]) := by decide +kernel

example (value : Env base [key, .nat, .list (.pair key .nat)]) :
    (lookupExpr comparison).denote primitives value = lookupValue value.1 value.2.1 value.2.2.1 := by
  simpa only [Expr.run_value] using
    lookupExpr_value primitives comparison comparison_correct value.1 value.2.1 value.2.2.1

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``EncodedLookup.certificate, ``EncodedLookup.bounds, ``EncodedLookup.budget_time,
      ``EncodedLookup.budget_words, ``EncodedLookup.primitiveNames, ``EncodedLookup.source_eq,
      ``EncodedLookup.compile, ``EncodedLookup.compile_isSome, ``EncodedLookup.bounded, ``EncodedLookup.names,
      ``EncodedLookup.staticMemory, ``EncodedLookup.memoryBound, ``comparison_correct, ``accepted, ``bounded] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperLookupExpression
