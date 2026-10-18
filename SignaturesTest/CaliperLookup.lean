import Signatures.Runtime.Caliper.LookupAcceptance
import Lean

open Caliper Signatures.Runtime Signatures.Runtime.CaliperBackend
open Signatures.Runtime.CaliperBackend.BoundedSource

namespace SignaturesTest.CaliperLookup

private def base (_ : Unit) : Type := Word 8
private inductive Op : Ty Unit → Ty Unit → Type
  | equal : Op (.pair .nat .nat) .bool
private def primitives : Primitives base Op where
  execute instruction := match instruction with | .equal => fun value => decide (value.1 = value.2)
  cost _ _ := 1

private def layout : LookupLayout 8 Nat Nat where
  key := Layout.counter 8 256 (by decide) (by decide)
  value := Layout.counter 8 256 (by decide) (by decide)
  capacity := 2
  wordFits := by decide
  countFits := by decide
  storageFits := by decide

private def comparison := SourceLookup.encodedComparison primitives (val := .nat) Op.equal layout (fun _ _ => rfl)
private def certificate := SourceLookup.certificate primitives (val := .nat) Op.equal layout comparison
private def budget := SourceLookup.encodedBudget primitives (val := .nat) Op.equal layout (fun _ _ => rfl)
private def bounds := SourceLookup.localBounds primitives (val := .nat) Op.equal layout comparison budget

private theorem emitted : certificate.Emits 7 :=
  SourceLookup.emits (base := base) (key := .nat) (val := .nat) primitives layout Op.equal comparison
    (SourceLookup.encodedNames primitives (val := .nat) Op.equal layout (fun _ _ => rfl)).buffers
private theorem accepted : (certificate.compile (by decide)).isSome := emitted.isSome
private def program := (certificate.compile (by decide)).get accepted

example : program.program.code.memBound ≤ 7 :=
  emitted.buffers program (Option.eq_some_of_isSome accepted)

private theorem bounded : program.BoundedBy 10853 39885 :=
  SourceLookup.bounded primitives (val := .nat) Op.equal layout comparison budget program (Option.eq_some_of_isSome accepted)
private theorem primitiveNames : certificate.PrimitiveNames 5 :=
  SourceLookup.primitiveNames primitives (val := .nat) Op.equal layout comparison
    (SourceLookup.encodedNames primitives (val := .nat) Op.equal layout (fun _ _ => rfl))

example : (certificate.budget bounds).time = 10853 ∧ (certificate.budget bounds).words = 39885 := by decide +kernel
example : NamesBound program.program.code 39890 :=
  certificate.nameBounds bounds primitiveNames program (Option.eq_some_of_isSome accepted)
example : staticWords program.program.code 5 201 ≤ 199445 :=
  certificate.staticMemory_bound bounds primitiveNames program (Option.eq_some_of_isSome accepted) 5 201

private def observe (value : layout.input.Value) := do
  let initial := layout.input.representation.initial value
  let before := { initial with
    bufs := fun buffer => if buffer = 200 then #[77] else initial.bufs buffer
    caps := fun buffer => if buffer = 200 then 1 else initial.caps buffer }
  let (state, time, net, peak) ← Caliper.run .unit RandomTape.zero 20000 program.program.code before
  pure ((state.bufs 0, state.bufs 200), (time, net, peak))

private def empty : layout.input.Value := ⟨(4, 9, [], ()), by
  change 4 < 256 ∧ 9 < 256 ∧ (0 ≤ 2 ∧ _) ∧ True
  simp⟩
private def miss : layout.input.Value := ⟨(4, 9, [(1, 7), (2, 8)], ()), by
  change 4 < 256 ∧ 9 < 256 ∧ (_ ≤ 2 ∧ ∀ p ∈ [(1, 7), (2, 8)], p.1 < 256 ∧ p.2 < 256) ∧ True
  decide⟩
private def zeroValue : layout.input.Value := ⟨(2, 9, [(1, 7), (2, 0)], ()), by
  change 2 < 256 ∧ 9 < 256 ∧ (_ ≤ 2 ∧ ∀ p ∈ [(1, 7), (2, 0)], p.1 < 256 ∧ p.2 < 256) ∧ True
  decide⟩
private def duplicate : layout.input.Value := ⟨(2, 9, [(2, 7), (2, 8)], ()), by
  change 2 < 256 ∧ 9 < 256 ∧ (_ ≤ 2 ∧ ∀ p ∈ [(2, 7), (2, 8)], p.1 < 256 ∧ p.2 < 256) ∧ True
  decide⟩

example : (observe empty).map Prod.fst = some (#[0, 9], #[77]) := by decide +kernel
example : (observe miss).map Prod.fst = some (#[0, 9], #[77]) := by decide +kernel
example : (observe zeroValue).map Prod.fst = some (#[1, 0], #[77]) := by decide +kernel
example : (observe duplicate).map Prod.fst = some (#[1, 7], #[77]) := by decide +kernel

example (value : Env base [.nat, .nat, .list (.pair .nat .nat)]) :
    (lookup Op.equal).denote primitives value = lookupValue value.1 value.2.1 value.2.2.1 :=
  SourceLookup.source_value primitives (val := .nat) Op.equal (fun _ _ => rfl) value

open Lean in
run_cmd do
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for name in [``LookupLayout.entry, ``LookupLayout.table, ``LookupLayout.input, ``LookupLayout.body,
      ``SourceLookup.certificate, ``SourceLookup.localBounds, ``SourceLookup.primitiveNames,
      ``SourceLookup.encodedComparison, ``SourceLookup.encodedBudget, ``SourceLookup.encodedNames,
      ``SourceLookup.source_value, ``SourceLookup.budget_time_eq, ``SourceLookup.budget_words_eq,
      ``SourceLookup.bounded, ``SourceLookup.emits, ``emitted, ``accepted, ``bounded, ``primitiveNames] do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "{name}: unexpected axiom {axiomName}"

end SignaturesTest.CaliperLookup
