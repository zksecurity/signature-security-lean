import Signatures.Runtime.Caliper.LookupCompilation

/-! Concrete polynomial budgets for the original lookup compiler. The table
width is determined by entry capacity, and every copied environment and stored
fold branch is charged. The comparison budget comes from its actual program. -/

namespace Signatures.Runtime.CaliperBackend.SourceLookup

open Caliper BoundedSource SourceExpression

def timeBudget (keyWords valueWords capacity comparisonTime : Nat) : Nat :=
  let tableWords := 1 + capacity * (keyWords + valueWords)
  188 * keyWords + 288 * valueWords + 256 * tableWords + 103 +
    capacity * (comparisonTime + 768 * keyWords + 1080 * valueWords + 428 * tableWords + 500)

def codeBudget (keyWords valueWords capacity comparisonWords : Nat) : Nat :=
  let tableWords := 1 + capacity * (keyWords + valueWords)
  611 * keyWords + 936 * valueWords + 832 * tableWords + 808 +
    capacity * (comparisonWords + 2678 * keyWords + 3770 * valueWords + 1521 * tableWords + 2589)

variable {w : Nat} {Atom : Type} {base : Atom → Type} {Op : Ty Atom → Ty Atom → Type}
    (P : Primitives base Op) {key val : Ty Atom} (eq : Op (.pair key key) .bool)
    (layout : LookupLayout w (key.Value base) (val.Value base))
    (comparison : Implementation .unit (layout.key.prod layout.key layout.keyPairFits) layout.boolean (P.execute eq))
    (budget : comparison.Budget)

theorem budget_time_eq :
    ((certificate P eq layout comparison).budget (localBounds P eq layout comparison budget)).time =
      timeBudget layout.key.representation.encoding.words layout.value.representation.encoding.words layout.capacity budget.estimate.time := by
  dsimp only [certificate, localBounds, bodyCode, testCode, foundCode, initialCode,
    entryCode, accumulatorCode, keyCode, defaultCode, tableCode, Compilation.budget, Variable.budget,
    Budget.storage, Budget.literal, Budget.seq, Budget.pair, Budget.branch, Budget.foldFrame, Budget.fixedFold, Budget.identity]
  simp only [Layout.prod_words, LookupLayout.entry_words, LookupLayout.result_words,
    LookupLayout.input_words, LookupLayout.valueTail_words, LookupLayout.tableTail_words, LookupLayout.table_words,
    LookupLayout.unit_words]
  dsimp [timeBudget, LookupLayout.width, ListFold.width, DataImplementation.boolLayout,
    Layout.all, Representation.transport, Encoding.transport, Representation.boolean, Encoding.boolean, Encoding.checked,
    FoldImplementation.bodyInput, Layout.prod, Representation.prod, Encoding.prod,
    LookupLayout.entry, LookupLayout.result, LookupLayout.input, LookupLayout.valueTail,
    LookupLayout.tableTail, LookupLayout.table, LookupLayout.unit, LookupLayout.boolean,
    Layout.boundedList, Representation.boundedList, Encoding.boundedList, DataImplementation.unitLayout, Encoding.unit]
  ring

theorem budget_words_eq :
    ((certificate P eq layout comparison).budget (localBounds P eq layout comparison budget)).words =
      codeBudget layout.key.representation.encoding.words layout.value.representation.encoding.words layout.capacity budget.estimate.words := by
  dsimp only [certificate, localBounds, bodyCode, testCode, foundCode, initialCode,
    entryCode, accumulatorCode, keyCode, defaultCode, tableCode, Compilation.budget, Variable.budget,
    Budget.storage, Budget.literal, Budget.seq, Budget.pair, Budget.branch, Budget.foldFrame, Budget.fixedFold, Budget.identity]
  simp only [Layout.prod_words, LookupLayout.entry_words, LookupLayout.result_words,
    LookupLayout.input_words, LookupLayout.valueTail_words, LookupLayout.tableTail_words, LookupLayout.table_words,
    LookupLayout.unit_words]
  dsimp [codeBudget, LookupLayout.width, ListFold.width, DataImplementation.boolLayout,
    Layout.all, Representation.transport, Encoding.transport, Representation.boolean, Encoding.boolean, Encoding.checked,
    FoldImplementation.bodyInput, Layout.prod, Representation.prod, Encoding.prod,
    LookupLayout.entry, LookupLayout.result, LookupLayout.input, LookupLayout.valueTail,
    LookupLayout.tableTail, LookupLayout.table, LookupLayout.unit, LookupLayout.boolean,
    Layout.boundedList, Representation.boundedList, Encoding.boundedList, DataImplementation.unitLayout, Encoding.unit]
  ring

theorem bounded (implementation : Implementation .unit layout.input layout.result ((lookup eq).denote P))
    (compiled : (certificate P eq layout comparison).compile (by decide) = some implementation) :
    implementation.BoundedBy
      (timeBudget layout.key.representation.encoding.words layout.value.representation.encoding.words layout.capacity budget.estimate.time)
      (codeBudget layout.key.representation.encoding.words layout.value.representation.encoding.words layout.capacity budget.estimate.words) := by
  rw [← budget_time_eq P eq layout comparison budget, ← budget_words_eq P eq layout comparison budget]
  exact (certificate P eq layout comparison).bounded (localBounds P eq layout comparison budget) implementation compiled

end Signatures.Runtime.CaliperBackend.SourceLookup
