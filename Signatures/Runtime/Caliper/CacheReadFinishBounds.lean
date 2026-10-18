import Signatures.Runtime.Caliper.CacheReadFinish

/-! Constructed local budgets for cache reads. Pairing budgets include all
shared-input copies; all formulas are linear in the stored layout widths. -/

namespace Signatures.Runtime.CaliperBackend.CacheRead

open Caliper BoundedSource

variable {w : Nat} {K V : Type} (layout : CacheLayout w K V)

def cachedBudget : (cached layout).Budget where
  estimate := (Budget.storage layout.lookup.result.representation.encoding.words).seq (Budget.storage layout.value.representation.encoding.words)
  bounded := (CacheFinish.result_bounded layout).then (Implementation.second_boundedBy _ _ _ _)

def oldTableBudget : (oldTable layout).Budget where
  estimate := (Budget.storage layout.lookup.input.representation.encoding.words).seq
    ⟨8 * layout.value.representation.encoding.words + 24 * layout.lookup.table.representation.encoding.words,
      26 * layout.value.representation.encoding.words + 78 * layout.lookup.table.representation.encoding.words + 44⟩
  bounded := (CacheFinish.original_bounded layout).then (CacheFinish.table_bounded layout)

def hitBudget : (hit layout).Budget where
  estimate := Budget.pair layout.lookup.accumulatorTail.representation.encoding.words
    layout.value.representation.encoding.words layout.lookup.table.representation.encoding.words
    (cachedBudget layout).estimate (oldTableBudget layout).estimate
  bounded := ((Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (cachedBudget layout).bounded (oldTableBudget layout).bounded).restrictInput
    layout.frameGuard).restrictInput (fun value => value.1.1 = true)

def freshBudget : (fresh layout).Budget := ⟨Budget.storage layout.value.representation.encoding.words, Implementation.first_boundedBy _ _ _ _⟩
def savedBudget : (saved layout).Budget := ⟨Budget.storage (no layout).representation.encoding.words, Implementation.second_boundedBy _ _ _ _⟩

def keyBudget : (key layout).Budget where
  estimate := (savedBudget layout).estimate.seq ((Budget.storage layout.lookup.input.representation.encoding.words).seq
    (Budget.storage layout.key.representation.encoding.words))
  bounded := (savedBudget layout).bounded.then
    (((CacheFinish.original_bounded layout).then (Implementation.first_boundedBy _ _ _ _)).restrictInput layout.frameGuard |>.restrictInput
      (fun value => value.1.1 = false))

def tableBudget : (table layout).Budget where
  estimate := (savedBudget layout).estimate.seq (oldTableBudget layout).estimate
  bounded := (savedBudget layout).bounded.then
    (((oldTableBudget layout).bounded.restrictInput layout.frameGuard).restrictInput (fun value => value.1.1 = false))

def entryBudget : (entry layout).Budget where
  estimate := Budget.pair (drawn layout).representation.encoding.words layout.key.representation.encoding.words
    layout.value.representation.encoding.words (keyBudget layout).estimate (freshBudget layout).estimate
  bounded := Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (keyBudget layout).bounded (freshBudget layout).bounded

def argumentsBudget : (arguments layout).Budget where
  estimate := Budget.pair (drawn layout).representation.encoding.words layout.lookup.entry.representation.encoding.words
    layout.lookup.table.representation.encoding.words (entryBudget layout).estimate (tableBudget layout).estimate
  bounded := Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (entryBudget layout).bounded (tableBudget layout).bounded

def insertedBudget : (inserted layout).Budget where
  estimate := (argumentsBudget layout).estimate.seq
    ⟨16 * (1 + (layout.capacityPred + 1) * layout.lookup.entry.representation.encoding.words) + 5,
      52 * (1 + (layout.capacityPred + 1) * layout.lookup.entry.representation.encoding.words) + 53⟩
  bounded := ((argumentsBudget layout).bounded.restrictOutput (fun value => value.2.length ≤ layout.capacityPred)
    (fun _ valid => valid.2.1.2 valid.2.2)).then (ListData.fixedCons_boundedBy _ _ _ _ _)

def finishBudget : (finish layout).Budget where
  estimate := Budget.pair (drawn layout).representation.encoding.words layout.value.representation.encoding.words
    layout.lookup.table.representation.encoding.words (freshBudget layout).estimate (insertedBudget layout).estimate
  bounded := Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (freshBudget layout).bounded (insertedBudget layout).bounded

def hitTime : Nat := 60 * layout.lookup.width + 112 * layout.value.representation.encoding.words +
  40 * layout.lookup.table.representation.encoding.words + 60
def hitWords : Nat := 195 * layout.lookup.width + 364 * layout.value.representation.encoding.words +
  130 * layout.lookup.table.representation.encoding.words + 407
def finishTime : Nat := 188 * layout.lookup.width + 80 * layout.key.representation.encoding.words +
  440 * layout.value.representation.encoding.words + 72 * layout.lookup.table.representation.encoding.words + 177
def finishWords : Nat := 611 * layout.lookup.width + 260 * layout.key.representation.encoding.words +
  1430 * layout.value.representation.encoding.words + 234 * layout.lookup.table.representation.encoding.words + 1131

theorem hit_bounded : (hit layout).BoundedBy (hitTime layout) (hitWords layout) := by
  apply (hitBudget layout).bounded.mono
  all_goals
    simp only [hitBudget, cachedBudget, oldTableBudget, Budget.pair, Budget.seq, Budget.storage,
      LookupLayout.input_words, LookupLayout.accumulatorTail_words, LookupLayout.result_words]
    dsimp only [hitTime, hitWords, CacheLayout.lookup]
    omega

theorem finish_bounded : (finish layout).BoundedBy (finishTime layout) (finishWords layout) := by
  apply (finishBudget layout).bounded.mono
  all_goals
    simp only [finishBudget, insertedBudget, argumentsBudget, entryBudget, tableBudget, keyBudget, savedBudget, freshBudget,
      oldTableBudget, Budget.pair, Budget.seq, Budget.storage, drawn_words, no_words, CacheLayout.frame_words,
      LookupLayout.input_words, LookupLayout.entry_words, LookupLayout.table_words]
    dsimp only [finishTime, finishWords, CacheLayout.lookup]
    simp only [LookupLayout.table_words]
    omega

theorem hit_names (slots : Nat) : NamesAccounted (hit layout).program.code slots := by
  have cachedNames : NamesAccounted (cached layout).program.code slots :=
    (Implementation.first_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)
  have tableNames : NamesAccounted (oldTable layout).program.code slots :=
    (Implementation.second_names _ _ _ _ _).seq
      (((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _))
  exact Implementation.pair_names (cached layout) (oldTable layout) layout.wordFits
    (nameFits layout _ (cached_buffers layout) (by decide)) (nameFits layout _ (oldTable_buffers layout) (by decide))
    (frame_duplicateFits layout) (frame_valueFits layout) (outputFits layout) cachedNames tableNames

theorem finish_names (slots : Nat) : NamesAccounted (finish layout).program.code slots := by
  have freshNames : NamesAccounted (fresh layout).program.code slots := Implementation.first_names _ _ _ _ _
  have savedNames : NamesAccounted (saved layout).program.code slots := Implementation.second_names _ _ _ _ _
  have keyNames : NamesAccounted (key layout).program.code slots :=
    savedNames.seq ((Implementation.second_names _ _ _ _ _).seq (Implementation.first_names _ _ _ _ _))
  have tableNames : NamesAccounted (table layout).program.code slots :=
    savedNames.seq ((Implementation.second_names _ _ _ _ _).seq
      (((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _)))
  have entryNames : NamesAccounted (entry layout).program.code slots :=
    Implementation.pair_names (key layout) (fresh layout) layout.wordFits
      (nameFits layout _ (key_buffers layout) (by decide)) (nameFits layout _ (fresh_buffers layout) (by decide))
      (drawn_duplicateFits layout) (drawn_keyFits layout)
      (layout.lookup.fits_of_le (by simp [LookupLayout.width]; dsimp [CacheLayout.lookup]; omega)) keyNames freshNames
  have argumentsNames : NamesAccounted (arguments layout).program.code slots :=
    Implementation.pair_names (entry layout) (table layout) layout.wordFits
      (nameFits layout _ (entry_buffers layout) (by decide)) (nameFits layout _ (table_buffers layout) (by decide))
      (drawn_duplicateFits layout) (drawn_entryFits layout) layout.entryTableFits entryNames tableNames
  have insertedNames : NamesAccounted (inserted layout).program.code slots :=
    argumentsNames.seq (ListData.fixedCons_names _ _ _ _ _ _)
  exact Implementation.pair_names (fresh layout) (inserted layout) layout.wordFits
    (nameFits layout _ (fresh_buffers layout) (by decide)) (nameFits layout _ (inserted_buffers layout) (by decide))
    (drawn_duplicateFits layout) (drawn_valueFits layout) (outputFits layout) freshNames insertedNames

end Signatures.Runtime.CaliperBackend.CacheRead
