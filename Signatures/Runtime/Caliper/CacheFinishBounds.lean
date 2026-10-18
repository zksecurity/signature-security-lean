import Signatures.Runtime.Caliper.CacheFinish

/-! Linear overhead for the fixed-capacity update following lookup. Every
projection is a paid copy; unchanged bytes only permit structural reassociation. -/

namespace Signatures.Runtime.CaliperBackend.CacheFinish

open Caliper BoundedSource

variable {w : Nat} {K V : Type} (layout : CacheLayout w K V)

theorem result_bounded : (result layout).BoundedBy
    (8 * layout.lookup.result.representation.encoding.words) (26 * layout.lookup.result.representation.encoding.words + 14) :=
  Implementation.first_boundedBy _ _ _ _

theorem original_bounded : (original layout).BoundedBy
    (8 * layout.lookup.input.representation.encoding.words) (26 * layout.lookup.input.representation.encoding.words + 14) :=
  Implementation.second_boundedBy _ _ _ _

theorem test_bounded : (test layout).BoundedBy
    (8 * layout.lookup.result.representation.encoding.words + 8)
    (26 * layout.lookup.result.representation.encoding.words + 55) := by
  refine (((result_bounded layout).then
    (Implementation.first_boundedBy layout.lookup.boolean layout.value layout.wordFits _)).restrictInput layout.frameGuard).mono ?_ ?_
  · rfl
  · simp only [LookupLayout.boolean_words]
    omega

theorem table_bounded : (table layout).BoundedBy
    (8 * layout.value.representation.encoding.words + 24 * layout.lookup.table.representation.encoding.words)
    (26 * layout.value.representation.encoding.words + 78 * layout.lookup.table.representation.encoding.words + 44) := by
  refine (((Implementation.second_boundedBy layout.key layout.lookup.valueTail layout.wordFits _).then
    (Implementation.second_boundedBy layout.value layout.lookup.tableTail layout.wordFits _)).then
      (Implementation.first_boundedBy layout.lookup.table layout.lookup.unit layout.wordFits _)).mono ?_ ?_
  all_goals simp only [LookupLayout.valueTail_words, LookupLayout.tableTail_words]; dsimp only [CacheLayout.lookup]; omega

theorem hit_bounded : (hit layout).BoundedBy
    (8 * layout.lookup.width + 8 * layout.value.representation.encoding.words + 24 * layout.lookup.table.representation.encoding.words)
    (26 * layout.lookup.width + 26 * layout.value.representation.encoding.words + 78 * layout.lookup.table.representation.encoding.words + 59) := by
  have bound := (((original_bounded layout).then
    (table_bounded layout)).restrictInput layout.frameGuard).restrictInput (fun value => value.1.1 = true)
  apply bound.mono <;> simp only [LookupLayout.input_words] <;> omega

theorem miss_bounded : (miss layout).BoundedBy
    (8 * layout.lookup.width + 16 * layout.lookup.table.representation.encoding.words + 5)
    (26 * layout.lookup.width + 52 * layout.lookup.table.representation.encoding.words + 70) := by
  have entryBound : (entryTable layout).BoundedBy 0 1 := ⟨fun _ => le_rfl, le_rfl⟩
  have prepared := (((original_bounded layout).then
    entryBound).restrictInput layout.frameGuard).restrictInput (fun value => value.1.1 = false)
  have room := prepared.restrictOutput (fun value => value.2.length ≤ layout.capacityPred) (fun _ valid => valid.1.2 valid.2)
  have inserted := room.then (ListData.fixedCons_boundedBy layout.lookup.entry layout.capacityPred layout.wordFits
    layout.countFits layout.fixedConsFits)
  apply inserted.mono
  all_goals
    simp only [LookupLayout.input_words, LookupLayout.table_words, LookupLayout.entry_words]
    dsimp only [CacheLayout.lookup]
    omega

def timeBudget : Nat := 92 * layout.lookup.width + 92 * layout.value.representation.encoding.words +
  40 * layout.lookup.table.representation.encoding.words + 140

def codeBudget : Nat := 325 * layout.lookup.width + 325 * layout.value.representation.encoding.words +
  130 * layout.lookup.table.representation.encoding.words + 787

theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  have bound := GuardedBranch.implementation_boundedBy (hw := layout.wordFits) (test layout) (test_nameFits layout)
    layout.frame_duplicateFits layout.frame_tagFits (hit layout) (miss layout)
    (test_bounded layout) (hit_bounded layout) (miss_bounded layout)
  apply bound.mono
  all_goals simp only [CacheLayout.frame_words, LookupLayout.result_words]; dsimp [timeBudget, codeBudget, CacheLayout.lookup]; omega

theorem table_buffers : (table layout).program.code.memBound ≤ 2 :=
  max_le (max_le (Implementation.second_buffers (by decide) _ _ layout.wordFits _)
    (Implementation.second_buffers (by decide) _ _ layout.wordFits _))
    (Implementation.first_buffers (by decide) _ _ layout.wordFits _)

theorem hit_buffers : (hit layout).program.code.memBound ≤ 2 :=
  max_le (Implementation.second_buffers (by decide) _ _ layout.wordFits _) (table_buffers layout)

theorem miss_buffers : (miss layout).program.code.memBound ≤ 2 :=
  max_le (max_le (Implementation.second_buffers (by decide) _ _ layout.wordFits _) (Nat.zero_le _))
    (ListData.fixedCons_buffers .unit (by decide) layout.lookup.entry layout.capacityPred layout.wordFits layout.countFits layout.fixedConsFits)

theorem buffers : (implementation layout).program.code.memBound ≤ 3 :=
  GuardedBranch.implementation_buffers (hw := layout.wordFits) (test layout) (test_nameFits layout)
    layout.frame_duplicateFits layout.frame_tagFits (hit layout) (miss layout)
    (test_buffers layout) (hit_buffers layout) (miss_buffers layout)

theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots := by
  have resultNames : NamesAccounted (result layout).program.code slots := Implementation.first_names _ _ _ _ _
  have originalNames : NamesAccounted (original layout).program.code slots := Implementation.second_names _ _ _ _ _
  have testNames : NamesAccounted (test layout).program.code slots :=
    resultNames.seq (Implementation.first_names _ _ _ _ _)
  have tableNames : NamesAccounted (table layout).program.code slots :=
    ((Implementation.second_names _ _ _ _ _).seq (Implementation.second_names _ _ _ _ _)).seq (Implementation.first_names _ _ _ _ _)
  have hitNames : NamesAccounted (hit layout).program.code slots := originalNames.seq tableNames
  have missNames : NamesAccounted (miss layout).program.code slots :=
    (originalNames.seq (skip_names slots)).seq (ListData.fixedCons_names _ _ _ _ _ _)
  exact GuardedBranch.implementation_names (hw := layout.wordFits) (test layout) (test_nameFits layout)
    layout.frame_duplicateFits layout.frame_tagFits (hit layout) (miss layout) testNames hitNames missNames

end Signatures.Runtime.CaliperBackend.CacheFinish
