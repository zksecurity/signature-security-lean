import Proofs.Runtime.Caliper.SyncWrapFinish

/-! Time, stored-code and name budgets of the finish. Every piece is a multiple of one unit:
the layout bound plus the budgets of the finishing routines, the two executed list lookups
and the executed reversal; the fold adds one such multiple per slot. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull

set_option linter.unusedSectionVars false

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  {core : Core w (key.Value base) M G (scalar.Value base) PK A}
  (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)
  (routines : Wrapper.FinishRoutines core)

namespace Wrapper

/-- One unit of time: the layout bound and every component budget. -/
def unitT : Nat := core.bound + routines.time + ListIndex.timeBudget (indexG (core := core)) + ListIndex.timeBudget (indexX (core := core)) +
  ListReverse.timeBudget (wrapper.revLayout outLe) + 1
/-- One unit of stored code. -/
def unitW : Nat := core.bound + routines.words + ListIndex.codeBudget (indexG (core := core)) + ListIndex.codeBudget (indexX (core := core)) +
  ListReverse.codeBudget (wrapper.revLayout outLe) + 1
/-- The name reservation covering every component. -/
def slotsAll : Nat := routines.slots + 3

local notation "T" => wrapper.unitT outLe routines
local notation "W" => wrapper.unitW outLe routines
local notation "S" => slotsAll routines
local notation "B" => core.bound

theorem routines_slots : routines.slots ≤ S := by simp only [slotsAll]; omega
theorem three_slots : 3 ≤ S := by simp only [slotsAll]; omega
theorem bound_le_T : B ≤ T := by simp only [unitT]; omega
theorem bound_le_W : B ≤ W := by simp only [unitW]; omega
theorem routines_le_T : routines.time ≤ T := by simp only [unitT]; omega
theorem routines_le_W : routines.words ≤ W := by simp only [unitW]; omega
theorem indexG_le_T : ListIndex.timeBudget (indexG (core := core)) ≤ T := by simp only [unitT]; omega
theorem indexG_le_W : ListIndex.codeBudget (indexG (core := core)) ≤ W := by simp only [unitW]; omega
theorem indexX_le_T : ListIndex.timeBudget (indexX (core := core)) ≤ T := by simp only [unitT]; omega
theorem indexX_le_W : ListIndex.codeBudget (indexX (core := core)) ≤ W := by simp only [unitW]; omega
theorem reverse_le_T : ListReverse.timeBudget (wrapper.revLayout outLe) ≤ T := by simp only [unitT]; omega
theorem reverse_le_W : ListReverse.codeBudget (wrapper.revLayout outLe) ≤ W := by simp only [unitW]; omega

/-! ## Widths -/
theorem tailIn_le : (tailIn (core := core)).representation.encoding.words ≤ B := by
  have := forgeryIn_words (core := core); have := core.forgeryAll_le; have := core.forgeryAll_words
  change core.scalar.representation.encoding.words + ((gammaIn (core := core)).representation.encoding.words +
    (xiIn (core := core)).representation.encoding.words) ≤ _
  omega
theorem explIn_le : (explIn (core := core)).representation.encoding.words ≤ B := by
  change (gammaIn (core := core)).representation.encoding.words + (xiIn (core := core)).representation.encoding.words ≤ _
  have := forgeryIn_words (core := core); have := core.forgeryAll_le; have := core.forgeryAll_words; omega
theorem counterOut_le : wrapper.counterOut.representation.encoding.words ≤ B := by rw [counterOut_words]; have := bound_pos (core := core); omega
theorem small_le : (Layout.counter w 2 (width_pos core.wordFits) (two_le (core := core))).representation.encoding.words ≤ B := by
  change 1 ≤ _; have := bound_pos (core := core); omega
theorem foldInput_le : (wrapper.foldInput outLe).representation.encoding.words ≤ 7 * B := by
  change core.slots.representation.encoding.words + ((wrapper.foldState outLe).representation.encoding.words +
    (foldEnv (core := core)).representation.encoding.words) ≤ _
  have := core.slots_le; have := wrapper.foldState_le outLe; have := foldEnv_le (core := core); have := bound_pos (core := core); omega
theorem foldState_le' : (wrapper.foldState outLe).representation.encoding.words ≤ 3 * B := by
  have := wrapper.foldState_le outLe; have := bound_pos (core := core); omega
include outLe in
theorem gammaOut_le' : wrapper.gammaOut.representation.encoding.words ≤ B := wrapper.gammaOut_le outLe
theorem slotEntry_cap : core.slotCap * core.slotEntry.representation.encoding.words ≤ B := (Nat.le_add_left _ 1).trans core.slots_le
theorem unit_words : (DataImplementation.unitLayout w).representation.encoding.words = 0 := rfl

set_option hygiene false in
/-- Close a budget inequality: every atom is a multiple of the bound or a component budget. -/
scoped macro "budget" : tactic => `(tactic| (
  have := wrapper.bound_le_T outLe routines; have := wrapper.bound_le_W outLe routines
  have := wrapper.routines_le_T outLe routines; have := wrapper.routines_le_W outLe routines
  have := wrapper.indexG_le_T outLe routines; have := wrapper.indexG_le_W outLe routines
  have := wrapper.indexX_le_T outLe routines; have := wrapper.indexX_le_W outLe routines
  have := wrapper.reverse_le_T outLe routines; have := wrapper.reverse_le_W outLe routines
  have := bound_pos (core := core)
  omega))

/-! ## Primitive certificates -/
theorem subtract_boundedBy (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    (Natural.subtract .unit left right hw leftFits rightFits).BoundedBy 8 38 :=
  ⟨fun value => (Natural.subtract_time_unit _ _ _ _ _ value).le, Saturating.descriptionWords_eq.le⟩
theorem subtract_names (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) (slots : Nat) :
    NamesAccounted (Natural.subtract .unit left right hw leftFits rightFits).program.code slots := by
  change NamesAccounted (Saturating.code (w := w)) slots
  have registers : registerSlots (Saturating.code (w := w)) ≤ 4 := by
    simp [Saturating.code, WordBinary.load, WordBinary.finish, registerSlots]
  have buffers : (Saturating.code (w := w)).memBound ≤ 3 := by
    simp [Saturating.code, WordBinary.load, WordBinary.finish, Stmt.memBound]
  have words : descriptionWords (Saturating.code (w := w)) = 38 := Saturating.descriptionWords_eq
  constructor <;> omega
theorem less_boundedBy (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    (Natural.less .unit left right hw leftFits rightFits).BoundedBy 6 27 :=
  ⟨fun value => (Natural.less_time_unit _ _ _ _ _ value).le, (WordBinary.descriptionWords_eq .ult).le⟩
theorem less_names (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) (slots : Nat) :
    NamesAccounted (Natural.less .unit left right hw leftFits rightFits).program.code slots := by
  change NamesAccounted (WordBinary.code (w := w) .ult) slots
  have registers : registerSlots (WordBinary.code (w := w) .ult) ≤ 3 := by
    simp [WordBinary.code, WordBinary.load, WordBinary.finish, registerSlots]
  have buffers : (WordBinary.code (w := w) .ult).memBound ≤ 1 := by
    simp [WordBinary.code, WordBinary.load, WordBinary.finish, Stmt.memBound]
  have words : descriptionWords (WordBinary.code (w := w) .ult) = 27 := WordBinary.descriptionWords_eq .ult
  constructor <;> omega
theorem unall_boundedBy {X : Type} (layout : Layout w X) : (Implementation.unall (width_pos core.wordFits) layout).BoundedBy 0 1 :=
  Implementation.recast_boundedBy _ _ _ _ _ _
theorem unall_names {X : Type} (layout : Layout w X) (slots : Nat) : NamesAccounted (Implementation.unall (width_pos core.wordFits) layout).program.code slots :=
  Implementation.recast_names _ _ _ _ _ _ slots
theorem lengthOut_boundedBy : wrapper.lengthOut.BoundedBy 14 40 := by
  constructor
  · intro _
    change (selectSlice (w := w) 0 1).staticTime .unit ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    omega
  · exact (selectSlice_descriptionWords 0 1).le
theorem lengthOut_names (slots : Nat) : NamesAccounted wrapper.lengthOut.program.code slots := selectSlice_names _ _ _

/-! ## Projections -/
theorem restState_boundedBy : (wrapper.restState outLe).BoundedBy (100 * T) (100 * W) :=
  (Implementation.first_boundedBy' _ _ (wrapper.foldState_le' outLe)).mono (by budget) (by budget)
theorem restEnv_boundedBy : (wrapper.restEnv outLe).BoundedBy (100 * T) (100 * W) :=
  (Implementation.second_boundedBy' _ _ (foldEnv_le (core := core))).mono (by budget) (by budget)
theorem restCounters_boundedBy : (wrapper.restCounters outLe).BoundedBy (200 * T) (200 * W) :=
  ((wrapper.restState_boundedBy outLe routines).then (Implementation.first_boundedBy' _ _ (counters_le (core := core)))).mono (by budget) (by budget)
theorem restAcc_boundedBy : (wrapper.restAcc outLe).BoundedBy (200 * T) (200 * W) :=
  ((wrapper.restState_boundedBy outLe routines).then (Implementation.second_boundedBy' _ _ (wrapper.gammaOut_le' outLe))).mono (by budget) (by budget)
theorem restRi_boundedBy : (wrapper.restRi outLe).BoundedBy (300 * T) (300 * W) :=
  ((wrapper.restCounters_boundedBy outLe routines).then (Implementation.first_boundedBy' _ _ (counterG_le (core := core)))).mono (by budget) (by budget)
theorem restRj_boundedBy : (wrapper.restRj outLe).BoundedBy (300 * T) (300 * W) :=
  ((wrapper.restCounters_boundedBy outLe routines).then (Implementation.second_boundedBy' _ _ (counterX_le (core := core)))).mono (by budget) (by budget)
theorem restGamma_boundedBy : (wrapper.restGamma outLe).BoundedBy (200 * T) (200 * W) :=
  ((wrapper.restEnv_boundedBy outLe routines).then (Implementation.first_boundedBy' _ _ (gammaIn_le (core := core)))).mono (by budget) (by budget)
theorem restXi_boundedBy : (wrapper.restXi outLe).BoundedBy (200 * T) (200 * W) :=
  ((wrapper.restEnv_boundedBy outLe routines).then (Implementation.second_boundedBy' _ _ (xiIn_le (core := core)))).mono (by budget) (by budget)
theorem restState_names : NamesAccounted (wrapper.restState outLe).program.code S := Implementation.first_names _ _ _ _ _
theorem restEnv_names : NamesAccounted (wrapper.restEnv outLe).program.code S := Implementation.second_names _ _ _ _ _
theorem restCounters_names : NamesAccounted (wrapper.restCounters outLe).program.code S :=
  (wrapper.restState_names outLe routines).seq (Implementation.first_names _ _ _ _ _)
theorem restAcc_names : NamesAccounted (wrapper.restAcc outLe).program.code S :=
  (wrapper.restState_names outLe routines).seq (Implementation.second_names _ _ _ _ _)
theorem restRi_names : NamesAccounted (wrapper.restRi outLe).program.code S :=
  (wrapper.restCounters_names outLe routines).seq (Implementation.first_names _ _ _ _ _)
theorem restRj_names : NamesAccounted (wrapper.restRj outLe).program.code S :=
  (wrapper.restCounters_names outLe routines).seq (Implementation.second_names _ _ _ _ _)
theorem restGamma_names : NamesAccounted (wrapper.restGamma outLe).program.code S :=
  (wrapper.restEnv_names outLe routines).seq (Implementation.first_names _ _ _ _ _)
theorem restXi_names : NamesAccounted (wrapper.restXi outLe).program.code S :=
  (wrapper.restEnv_names outLe routines).seq (Implementation.second_names _ _ _ _ _)

/-! ## Positions -/
theorem capGConst_boundedBy : (wrapper.capGConst outLe).BoundedBy (3 * T) (3 * W) :=
  (Natural.constant_boundedBy _ _ _ _ _ _).mono (by budget) (by budget)
theorem capXConst_boundedBy : (wrapper.capXConst outLe).BoundedBy (3 * T) (3 * W) :=
  (Natural.constant_boundedBy _ _ _ _ _ _).mono (by budget) (by budget)
theorem oneConst_boundedBy : (wrapper.oneConst outLe).BoundedBy (3 * T) (3 * W) :=
  (Natural.constant_boundedBy _ _ _ _ _ _).mono (by budget) (by budget)
theorem capGConst_names : NamesAccounted (wrapper.capGConst outLe).program.code S := Natural.constant_names _ _ _ _ _ _ _
theorem capXConst_names : NamesAccounted (wrapper.capXConst outLe).program.code S := Natural.constant_names _ _ _ _ _ _ _
theorem oneConst_names : NamesAccounted (wrapper.oneConst outLe).program.code S := Natural.constant_names _ _ _ _ _ _ _
theorem indexOfG_boundedBy : (wrapper.indexOfG outLe).BoundedBy (2000 * T) (2000 * W) := by
  unfold indexOfG
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.capGConst_boundedBy outLe routines) (wrapper.restRi_boundedBy outLe routines)
    (wrapper.rest_le outLe) (counterG_le (core := core)) (counterG_le (core := core))).then (subtract_boundedBy _ _ _ _ _)).mono ?_ ?_
  all_goals budget
theorem indexOfX_boundedBy : (wrapper.indexOfX outLe).BoundedBy (2000 * T) (2000 * W) := by
  unfold indexOfX
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.capXConst_boundedBy outLe routines) (wrapper.restRj_boundedBy outLe routines)
    (wrapper.rest_le outLe) (counterX_le (core := core)) (counterX_le (core := core))).then (subtract_boundedBy _ _ _ _ _)).mono ?_ ?_
  all_goals budget
theorem decG_boundedBy : (wrapper.decG outLe).BoundedBy (2000 * T) (2000 * W) := by
  unfold decG
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.restRi_boundedBy outLe routines) (wrapper.oneConst_boundedBy outLe routines)
    (wrapper.rest_le outLe) (counterG_le (core := core)) (small_le (core := core))).then (subtract_boundedBy _ _ _ _ _)).mono ?_ ?_
  all_goals budget
theorem decX_boundedBy : (wrapper.decX outLe).BoundedBy (2000 * T) (2000 * W) := by
  unfold decX
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.restRj_boundedBy outLe routines) (wrapper.oneConst_boundedBy outLe routines)
    (wrapper.rest_le outLe) (counterX_le (core := core)) (small_le (core := core))).then (subtract_boundedBy _ _ _ _ _)).mono ?_ ?_
  all_goals budget
theorem indexOfG_names : NamesAccounted (wrapper.indexOfG outLe).program.code S :=
  (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.capGConst_names outLe routines) (wrapper.restRi_names outLe routines)).seq (subtract_names _ _ _ _ _ _)
theorem indexOfX_names : NamesAccounted (wrapper.indexOfX outLe).program.code S :=
  (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.capXConst_names outLe routines) (wrapper.restRj_names outLe routines)).seq (subtract_names _ _ _ _ _ _)
theorem decG_names : NamesAccounted (wrapper.decG outLe).program.code S :=
  (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.restRi_names outLe routines) (wrapper.oneConst_names outLe routines)).seq (subtract_names _ _ _ _ _ _)
theorem decX_names : NamesAccounted (wrapper.decX outLe).program.code S :=
  (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.restRj_names outLe routines) (wrapper.oneConst_names outLe routines)).seq (subtract_names _ _ _ _ _ _)

/-! ## Coefficients -/
theorem zeroScalar_boundedBy : (wrapper.zeroScalar outLe).BoundedBy (100 * T) (100 * W) :=
  (Implementation.constant_bounded' _ _ (scalar_le (core := core))).mono (by budget) (by budget)
theorem zeroScalar_names : NamesAccounted (wrapper.zeroScalar outLe).program.code S := Implementation.constant_names _ _ _ _ _
theorem lookupG_boundedBy : (wrapper.lookupG outLe).BoundedBy (6000 * T) (6000 * W) := by
  unfold lookupG
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.indexOfG_boundedBy outLe routines)
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.zeroScalar_boundedBy outLe routines) (wrapper.restGamma_boundedBy outLe routines)
      (wrapper.rest_le outLe) (scalar_le (core := core)) (gammaIn_le (core := core)))
    (wrapper.rest_le outLe) (counterG_le (core := core)) (Layout.prod_le' _ _ _ (scalar_le (core := core)) (gammaIn_le (core := core)))).then
    (ListIndex.bounded (indexG (core := core)))).mono ?_ ?_
  all_goals budget
theorem lookupX_boundedBy : (wrapper.lookupX outLe).BoundedBy (6000 * T) (6000 * W) := by
  unfold lookupX
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.indexOfX_boundedBy outLe routines)
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.zeroScalar_boundedBy outLe routines) (wrapper.restXi_boundedBy outLe routines)
      (wrapper.rest_le outLe) (scalar_le (core := core)) (xiIn_le (core := core)))
    (wrapper.rest_le outLe) (counterX_le (core := core)) (Layout.prod_le' _ _ _ (scalar_le (core := core)) (xiIn_le (core := core)))).then
    (ListIndex.bounded (indexX (core := core)))).mono ?_ ?_
  all_goals budget
theorem lookupG_names : NamesAccounted (wrapper.lookupG outLe).program.code S :=
  (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.indexOfG_names outLe routines)
    (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.zeroScalar_names outLe routines) (wrapper.restGamma_names outLe routines))).seq
    (ListIndex.names (indexG (core := core)) _)
theorem lookupX_names : NamesAccounted (wrapper.lookupX outLe).program.code S :=
  (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.indexOfX_names outLe routines)
    (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.zeroScalar_names outLe routines) (wrapper.restXi_names outLe routines))).seq
    (ListIndex.names (indexX (core := core)) _)

/-! ## Guarded cons -/
theorem capOutConst_boundedBy : wrapper.capOutConst.BoundedBy (3 * T) (3 * W) :=
  (Natural.constant_boundedBy _ _ _ _ _ _).mono (by budget) (by budget)
theorem capOutConst_names : NamesAccounted wrapper.capOutConst.program.code S := Natural.constant_names _ _ _ _ _ _ _
theorem hasRoomOut_boundedBy : (wrapper.hasRoomOut outLe).BoundedBy (1000 * T) (1000 * W) := by
  unfold hasRoomOut
  refine ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ wrapper.lengthOut_boundedBy (wrapper.capOutConst_boundedBy outLe routines)
    (wrapper.gammaOut_le' outLe) wrapper.counterOut_le wrapper.counterOut_le).then (less_boundedBy _ _ _ _ _)).mono ?_ ?_
  all_goals budget
theorem hasRoomOut_names : NamesAccounted (wrapper.hasRoomOut outLe).program.code S :=
  (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.lengthOut_names _) (wrapper.capOutConst_names routines)).seq (less_names _ _ _ _ _ _)
theorem roomTestOut_boundedBy : (wrapper.roomTestOut outLe).BoundedBy (1200 * T) (1200 * W) := by
  unfold roomTestOut
  refine ((Implementation.second_boundedBy' _ _ (wrapper.gammaOut_le' outLe)).then (wrapper.hasRoomOut_boundedBy outLe routines)).mono ?_ ?_
  all_goals budget
theorem roomTestOut_names : NamesAccounted (wrapper.roomTestOut outLe).program.code S :=
  (Implementation.second_names _ _ _ _ _).seq (wrapper.hasRoomOut_names outLe routines)
theorem consGuard_boundedBy : (wrapper.consGuard outLe).BoundedBy (3000 * T) (3000 * W) := by
  unfold consGuard
  have hg : wrapper.gammaOut.representation.encoding.words = 1 + (wrapper.caps.gammaPred + 1) * core.scalar.representation.encoding.words := rfl
  refine (Implementation.BoundedBy.castFunction (GuardedBranch.implementation_boundedBy _ _ _ _ _ _ (wrapper.roomTestOut_boundedBy outLe routines)
    ((Implementation.view_boundedBy _ _ _).then (ListData.fixedCons_boundedBy core.scalar wrapper.caps.gammaPred core.wordFits wrapper.capOut_lt (wrapper.fixedFrameFits outLe)))
    ((Implementation.second_boundedBy' _ _ (wrapper.gammaOut_le' outLe)).restrictInput _)) _).mono ?_ ?_
  all_goals
    have := wrapper.consInput_le outLe; have := wrapper.gammaOut_le' outLe
    budget
theorem consGuard_names : NamesAccounted (wrapper.consGuard outLe).program.code S :=
  Implementation.castFunction_names _ _ (GuardedBranch.implementation_names _ _ _ _ _ _ (wrapper.roomTestOut_names outLe routines)
    ((Implementation.view_names _ _ _ _).seq (ListData.fixedCons_names _ _ _ _ _ _))
    (Implementation.restrictInput_names _ _ (Implementation.second_names _ _ _ _ _)))

/-! ## The body and the fold -/
theorem hashRest_boundedBy : (wrapper.hashRest outLe).BoundedBy (200 * T) (200 * W) :=
  (Implementation.second_boundedBy' _ _ (wrapper.rest_le outLe)).mono (by budget) (by budget)
theorem signRest_boundedBy : (wrapper.signRest outLe).BoundedBy (200 * T) (200 * W) :=
  (Implementation.second_boundedBy' _ _ (wrapper.rest_le outLe)).mono (by budget) (by budget)
theorem signEntry_boundedBy : (wrapper.signEntry outLe).BoundedBy (100 * T) (100 * W) :=
  (Implementation.first_boundedBy' _ _ (scalar_le (core := core))).mono (by budget) (by budget)
theorem hashRest_names : NamesAccounted (wrapper.hashRest outLe).program.code S := Implementation.second_names _ _ _ _ _
theorem signRest_names : NamesAccounted (wrapper.signRest outLe).program.code S := Implementation.second_names _ _ _ _ _
theorem signEntry_names : NamesAccounted (wrapper.signEntry outLe).program.code S := Implementation.first_names _ _ _ _ _

theorem hashStep_boundedBy : (wrapper.hashStep outLe).BoundedBy (20000 * T) (20000 * W) := by
  unfold hashStep
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((wrapper.hashRest_boundedBy outLe routines).then (wrapper.decG_boundedBy outLe routines))
      ((wrapper.hashRest_boundedBy outLe routines).then (wrapper.restRj_boundedBy outLe routines))
      (wrapper.hashInput_le outLe) (counterG_le (core := core)) (counterX_le (core := core)))
    ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((wrapper.hashRest_boundedBy outLe routines).then (wrapper.lookupG_boundedBy outLe routines))
      ((wrapper.hashRest_boundedBy outLe routines).then (wrapper.restAcc_boundedBy outLe routines))
      (wrapper.hashInput_le outLe) (scalar_le (core := core)) (wrapper.gammaOut_le' outLe)).then (wrapper.consGuard_boundedBy outLe routines))
    (wrapper.hashInput_le outLe) (Layout.prod_le' _ _ _ (counterG_le (core := core)) (counterX_le (core := core))) (wrapper.gammaOut_le' outLe)).mono ?_ ?_
  all_goals budget
theorem signStep_boundedBy : (wrapper.signStep outLe routines).BoundedBy (20000 * T) (20000 * W) := by
  unfold signStep
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((wrapper.signRest_boundedBy outLe routines).then (wrapper.restRi_boundedBy outLe routines))
      ((wrapper.signRest_boundedBy outLe routines).then (wrapper.decX_boundedBy outLe routines))
      (wrapper.signInput_le outLe) (counterG_le (core := core)) (counterX_le (core := core)))
    ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _
      ((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((wrapper.signRest_boundedBy outLe routines).then (wrapper.lookupX_boundedBy outLe routines))
        (wrapper.signEntry_boundedBy outLe routines) (wrapper.signInput_le outLe) (scalar_le (core := core)) (scalar_le (core := core))).then routines.mulBound)
      ((wrapper.signRest_boundedBy outLe routines).then (wrapper.restAcc_boundedBy outLe routines))
      (wrapper.signInput_le outLe) (scalar_le (core := core)) (wrapper.gammaOut_le' outLe)).then (wrapper.consGuard_boundedBy outLe routines))
    (wrapper.signInput_le outLe) (Layout.prod_le' _ _ _ (counterG_le (core := core)) (counterX_le (core := core))) (wrapper.gammaOut_le' outLe)).mono ?_ ?_
  all_goals budget
theorem hashStep_names : NamesAccounted (wrapper.hashStep outLe).program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _
    (Implementation.pair'_names _ _ _ _ _ _ _ ((wrapper.hashRest_names outLe routines).seq (wrapper.decG_names outLe routines))
      ((wrapper.hashRest_names outLe routines).seq (wrapper.restRj_names outLe routines)))
    ((Implementation.pair'_names _ _ _ _ _ _ _ ((wrapper.hashRest_names outLe routines).seq (wrapper.lookupG_names outLe routines))
      ((wrapper.hashRest_names outLe routines).seq (wrapper.restAcc_names outLe routines))).seq (wrapper.consGuard_names outLe routines))
theorem signStep_names : NamesAccounted (wrapper.signStep outLe routines).program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _
    (Implementation.pair'_names _ _ _ _ _ _ _ ((wrapper.signRest_names outLe routines).seq (wrapper.restRi_names outLe routines))
      ((wrapper.signRest_names outLe routines).seq (wrapper.decX_names outLe routines)))
    ((Implementation.pair'_names _ _ _ _ _ _ _
      ((Implementation.pair'_names _ _ _ _ _ _ _ ((wrapper.signRest_names outLe routines).seq (wrapper.lookupX_names outLe routines))
        (wrapper.signEntry_names outLe routines)).seq (routines.mulNames.mono (routines_slots routines)))
      ((wrapper.signRest_names outLe routines).seq (wrapper.restAcc_names outLe routines))).seq (wrapper.consGuard_names outLe routines))

theorem body_boundedBy : (wrapper.body outLe routines).BoundedBy (60000 * T) (60000 * W) := by
  unfold body
  refine (Implementation.BoundedBy.castFunction ((Implementation.distribute_boundedBy' _ _ _ (le_of_eq unit_words) (scalar_le (core := core)) (wrapper.rest_le outLe)).then
    (Implementation.branch_boundedBy' _ _ _ _ (wrapper.hashStep_boundedBy outLe routines) (wrapper.signStep_boundedBy outLe routines)
      (wrapper.hashInput_le outLe) (wrapper.signInput_le outLe))) _).mono ?_ ?_
  all_goals budget
theorem body_names : NamesAccounted (wrapper.body outLe routines).program.code S :=
  Implementation.castFunction_names _ _ (((Implementation.distribute_names _ _ _ _ _).mono (three_slots routines)).seq
    (Implementation.branch_names _ _ _ _ (wrapper.hashStep_names outLe routines) (wrapper.signStep_names outLe routines)))

theorem fold_width : ListFold.width core.slotEntry.representation.encoding.words (wrapper.foldState outLe).representation.encoding.words
    (foldEnv (core := core)).representation.encoding.words core.slotCap ≤ 20 * B := by
  unfold ListFold.width
  rw [Nat.add_mul, one_mul]
  have := slotEntry_cap (core := core); have := core.slotEntry_le; have := wrapper.foldState_le' outLe; have := foldEnv_le (core := core)
  have := bound_pos (core := core); omega
/-- The fold's budget: one unit per slot beyond a fixed overhead. -/
theorem fold_boundedBy : (wrapper.fold outLe routines).BoundedBy (100 * T + core.slotCap * (70000 * T)) (100 * W + core.slotCap * (70000 * W)) := by
  unfold fold
  refine (FoldImplementation.compile_boundedBy _ _ _ _ _ _ _ _ _ _ _ _ (wrapper.body_boundedBy outLe routines)).mono ?_ ?_
  · have step := Nat.mul_le_mul_left core.slotCap (show 60000 * T + 44 * ListFold.width core.slotEntry.representation.encoding.words
        (wrapper.foldState outLe).representation.encoding.words (foldEnv (core := core)).representation.encoding.words core.slotCap + 7 ≤ 70000 * T by
      have := wrapper.fold_width outLe; budget)
    have := wrapper.foldState_le' outLe; budget
  · have step := Nat.mul_le_mul_left core.slotCap (show 60000 * W + 169 * ListFold.width core.slotEntry.representation.encoding.words
        (wrapper.foldState outLe).representation.encoding.words (foldEnv (core := core)).representation.encoding.words core.slotCap + 115 ≤ 70000 * W by
      have := wrapper.fold_width outLe; budget)
    have := wrapper.foldState_le' outLe; budget
theorem fold_names : NamesAccounted (wrapper.fold outLe routines).program.code S :=
  FoldImplementation.compile_names _ _ _ _ _ _ _ _ _ _ (wrapper.body_names outLe routines)

/-! ## The finish -/
theorem inForgery_boundedBy : (inForgery (core := core)).BoundedBy (100 * T) (100 * W) :=
  (Implementation.first_boundedBy' _ _ core.forgeryAll_le).mono (by budget) (by budget)
theorem inKeyed_boundedBy : (inKeyed (core := core)).BoundedBy (100 * T) (100 * W) :=
  (Implementation.second_boundedBy' _ _ core.keyed_le).mono (by budget) (by budget)
theorem inD_boundedBy : (inD (core := core)).BoundedBy (300 * T) (300 * W) :=
  (((wrapper.inKeyed_boundedBy outLe routines).then (Implementation.first_boundedBy' _ _ core.scalarAll_le)).then (unall_boundedBy (core := core) _)).mono (by budget) (by budget)
theorem inSlots_boundedBy : (inSlots (core := core)).BoundedBy (300 * T) (300 * W) :=
  ((wrapper.inKeyed_boundedBy outLe routines).then (Implementation.second_boundedBy' _ _ core.slots_le)).mono (by budget) (by budget)
theorem inForgery_names : NamesAccounted (inForgery (core := core)).program.code S := Implementation.first_names _ _ _ _ _
theorem inKeyed_names : NamesAccounted (inKeyed (core := core)).program.code S := Implementation.second_names _ _ _ _ _
theorem inD_names : NamesAccounted (inD (core := core)).program.code S :=
  ((inKeyed_names routines).seq (Implementation.first_names _ _ _ _ _)).seq (unall_names (core := core) _ _)
theorem inSlots_names : NamesAccounted (inSlots (core := core)).program.code S :=
  (inKeyed_names routines).seq (Implementation.second_names _ _ _ _ _)

theorem fMessage_boundedBy : (fMessage (core := core)).BoundedBy (100 * T) (100 * W) :=
  ((Implementation.allFirst_boundedBy' _ _ (message_le (core := core))).then (unall_boundedBy (core := core) _)).mono (by budget) (by budget)
theorem fTail_boundedBy : (fTail (core := core)).BoundedBy (100 * T) (100 * W) :=
  (Implementation.allSecond_boundedBy' _ _ (tailIn_le (core := core))).mono (by budget) (by budget)
theorem fBeta_boundedBy : (fBeta (core := core)).BoundedBy (300 * T) (300 * W) :=
  (((wrapper.fTail_boundedBy outLe routines).then (Implementation.allFirst_boundedBy' _ _ (scalar_le (core := core)))).then (unall_boundedBy (core := core) _)).mono (by budget) (by budget)
theorem fExpl_boundedBy : (fExpl (core := core)).BoundedBy (300 * T) (300 * W) :=
  ((wrapper.fTail_boundedBy outLe routines).then (Implementation.allSecond_boundedBy' _ _ (explIn_le (core := core)))).mono (by budget) (by budget)
theorem fGamma_boundedBy : (fGamma (core := core)).BoundedBy (500 * T) (500 * W) :=
  (((wrapper.fExpl_boundedBy outLe routines).then (Implementation.allFirst_boundedBy' _ _ (gammaIn_le (core := core)))).then (unall_boundedBy (core := core) _)).mono (by budget) (by budget)
theorem fXi_boundedBy : (fXi (core := core)).BoundedBy (500 * T) (500 * W) :=
  (((wrapper.fExpl_boundedBy outLe routines).then (Implementation.allSecond_boundedBy' _ _ (xiIn_le (core := core)))).then (unall_boundedBy (core := core) _)).mono (by budget) (by budget)
theorem fMessage_names : NamesAccounted (fMessage (core := core)).program.code S := (Implementation.allFirst_names _ _ _ _ _).seq (unall_names (core := core) _ _)
theorem fTail_names : NamesAccounted (fTail (core := core)).program.code S := Implementation.allSecond_names _ _ _ _ _
theorem fBeta_names : NamesAccounted (fBeta (core := core)).program.code S :=
  ((fTail_names routines).seq (Implementation.allFirst_names _ _ _ _ _)).seq (unall_names (core := core) _ _)
theorem fExpl_names : NamesAccounted (fExpl (core := core)).program.code S := (fTail_names routines).seq (Implementation.allSecond_names _ _ _ _ _)
theorem fGamma_names : NamesAccounted (fGamma (core := core)).program.code S :=
  ((fExpl_names routines).seq (Implementation.allFirst_names _ _ _ _ _)).seq (unall_names (core := core) _ _)
theorem fXi_names : NamesAccounted (fXi (core := core)).program.code S :=
  ((fExpl_names routines).seq (Implementation.allSecond_names _ _ _ _ _)).seq (unall_names (core := core) _ _)

theorem capGConst'_boundedBy : (capGConst' (core := core)).BoundedBy (3 * T) (3 * W) := (Natural.constant_boundedBy _ _ _ _ _ _).mono (by budget) (by budget)
theorem capXConst'_boundedBy : (capXConst' (core := core)).BoundedBy (3 * T) (3 * W) := (Natural.constant_boundedBy _ _ _ _ _ _).mono (by budget) (by budget)
theorem emptyOut_boundedBy : wrapper.emptyOut.BoundedBy (100 * T) (100 * W) :=
  (Implementation.constant_bounded' _ _ (wrapper.gammaOut_le' outLe)).mono (by budget) (by budget)
theorem capGConst'_names : NamesAccounted (capGConst' (core := core)).program.code S := Natural.constant_names _ _ _ _ _ _ _
theorem capXConst'_names : NamesAccounted (capXConst' (core := core)).program.code S := Natural.constant_names _ _ _ _ _ _ _
theorem emptyOut_names : NamesAccounted wrapper.emptyOut.program.code S := Implementation.constant_names _ _ _ _ _
theorem initState_boundedBy : (wrapper.initState outLe).BoundedBy (2000 * T) (2000 * W) := by
  unfold initState
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.capGConst'_boundedBy outLe routines) (wrapper.capXConst'_boundedBy outLe routines)
      (finalInput_le' (core := core)) (counterG_le (core := core)) (counterX_le (core := core)))
    (wrapper.emptyOut_boundedBy outLe routines) (finalInput_le' (core := core)) (counters_le (core := core)) (wrapper.gammaOut_le' outLe)).mono ?_ ?_
  all_goals budget
theorem initEnv_boundedBy : (wrapper.initEnv outLe).BoundedBy (3000 * T) (3000 * W) := by
  unfold initEnv
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((wrapper.inForgery_boundedBy outLe routines).then (wrapper.fGamma_boundedBy outLe routines))
    ((wrapper.inForgery_boundedBy outLe routines).then (wrapper.fXi_boundedBy outLe routines))
    (finalInput_le' (core := core)) (gammaIn_le (core := core)) (xiIn_le (core := core))).mono ?_ ?_
  all_goals budget
theorem initState_names : NamesAccounted (wrapper.initState outLe).program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _ (Implementation.pair'_names _ _ _ _ _ _ _ (capGConst'_names routines) (capXConst'_names routines))
    (wrapper.emptyOut_names routines)
theorem initEnv_names : NamesAccounted (wrapper.initEnv outLe).program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _ ((inForgery_names routines).seq (fGamma_names routines))
    ((inForgery_names routines).seq (fXi_names routines))
theorem prep_boundedBy : (wrapper.prep outLe).BoundedBy (10000 * T) (10000 * W) := by
  unfold prep
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.inSlots_boundedBy outLe routines)
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.initState_boundedBy outLe routines) (wrapper.initEnv_boundedBy outLe routines)
      (finalInput_le' (core := core)) (wrapper.foldState_le' outLe) (foldEnv_le (core := core)))
    (finalInput_le' (core := core)) core.slots_le (Layout.prod_le' _ _ _ (wrapper.foldState_le' outLe) (foldEnv_le (core := core)))).mono ?_ ?_
  all_goals budget
theorem prep_names : NamesAccounted (wrapper.prep outLe).program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _ (inSlots_names routines)
    (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.initState_names outLe routines) (wrapper.initEnv_names outLe routines))

/-- The per-slot part of the finish's budget. -/
def perSlotT : Nat := 70000 * T
def perSlotW : Nat := 70000 * W
theorem accOut_boundedBy : (wrapper.accOut outLe routines).BoundedBy (11000 * T + core.slotCap * wrapper.perSlotT outLe routines)
    (11000 * W + core.slotCap * wrapper.perSlotW outLe routines) := by
  unfold accOut
  refine (((wrapper.prep_boundedBy outLe routines).then (wrapper.fold_boundedBy outLe routines)).then
    (Implementation.second_boundedBy' _ _ (wrapper.gammaOut_le' outLe))).mono ?_ ?_
  all_goals simp only [perSlotT, perSlotW]; budget
theorem accOut_names : NamesAccounted (wrapper.accOut outLe routines).program.code S :=
  ((wrapper.prep_names outLe routines).seq (wrapper.fold_names outLe routines)).seq (Implementation.second_names _ _ _ _ _)
theorem finScalar_boundedBy : (wrapper.finScalar outLe routines).BoundedBy (2000 * T) (2000 * W) := by
  unfold finScalar
  refine (((Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.inD_boundedBy outLe routines)
    ((wrapper.inForgery_boundedBy outLe routines).then (wrapper.fMessage_boundedBy outLe routines))
    (finalInput_le' (core := core)) (scalar_le (core := core)) (message_le (core := core))).then routines.finBound).then routines.negBound).mono ?_ ?_
  all_goals budget
theorem finScalar_names : NamesAccounted (wrapper.finScalar outLe routines).program.code S :=
  ((Implementation.pair'_names _ _ _ _ _ _ _ (inD_names routines) ((inForgery_names routines).seq (fMessage_names routines))).seq
    (routines.finNames.mono (routines_slots routines))).seq (routines.negNames.mono (routines_slots routines))
theorem consFinal_boundedBy : (wrapper.consFinal outLe routines).BoundedBy (15000 * T + core.slotCap * wrapper.perSlotT outLe routines)
    (15000 * W + core.slotCap * wrapper.perSlotW outLe routines) := by
  unfold consFinal
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.finScalar_boundedBy outLe routines) (wrapper.accOut_boundedBy outLe routines)
    (finalInput_le' (core := core)) (scalar_le (core := core)) (wrapper.gammaOut_le' outLe)).mono ?_ ?_
  all_goals budget
theorem consFinal_names : NamesAccounted (wrapper.consFinal outLe routines).program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.finScalar_names outLe routines) (wrapper.accOut_names outLe routines)
theorem consed_boundedBy : (wrapper.consed outLe routines).BoundedBy (20000 * T + core.slotCap * wrapper.perSlotT outLe routines)
    (20000 * W + core.slotCap * wrapper.perSlotW outLe routines) := by
  unfold consed
  refine ((wrapper.consFinal_boundedBy outLe routines).then (wrapper.consGuard_boundedBy outLe routines)).mono ?_ ?_
  all_goals budget
theorem consed_names : NamesAccounted (wrapper.consed outLe routines).program.code S :=
  (wrapper.consFinal_names outLe routines).seq (wrapper.consGuard_names outLe routines)
theorem reverseOut_boundedBy : (wrapper.reverseOut outLe).BoundedBy T W :=
  (ListReverse.bounded _).mono (wrapper.reverse_le_T outLe routines) (wrapper.reverse_le_W outLe routines)
theorem reverseOut_names : NamesAccounted (wrapper.reverseOut outLe).program.code S := ListReverse.names _ _
theorem gammaFinal_boundedBy : (wrapper.gammaFinal outLe routines).BoundedBy (21000 * T + core.slotCap * wrapper.perSlotT outLe routines)
    (21000 * W + core.slotCap * wrapper.perSlotW outLe routines) := by
  unfold gammaFinal
  refine ((wrapper.consed_boundedBy outLe routines).then (wrapper.reverseOut_boundedBy outLe routines)).mono ?_ ?_
  all_goals budget
theorem gammaFinal_names : NamesAccounted (wrapper.gammaFinal outLe routines).program.code S :=
  (wrapper.consed_names outLe routines).seq (wrapper.reverseOut_names outLe routines)

/-- The finish's budgets. -/
def finishTime : Nat := 30000 * T + core.slotCap * wrapper.perSlotT outLe routines
def finishWords : Nat := 30000 * W + core.slotCap * wrapper.perSlotW outLe routines
theorem finish_boundedBy : (wrapper.finish outLe routines).BoundedBy (wrapper.finishTime outLe routines) (wrapper.finishWords outLe routines) := by
  unfold finish
  refine (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((wrapper.inForgery_boundedBy outLe routines).then (wrapper.fMessage_boundedBy outLe routines))
    (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ ((wrapper.inForgery_boundedBy outLe routines).then (wrapper.fBeta_boundedBy outLe routines))
      (Implementation.pair'_boundedBy' _ _ _ _ _ _ _ (wrapper.gammaFinal_boundedBy outLe routines)
        ((wrapper.inForgery_boundedBy outLe routines).then (wrapper.fXi_boundedBy outLe routines))
        (finalInput_le' (core := core)) (wrapper.gammaOut_le' outLe) (xiIn_le (core := core)))
      (finalInput_le' (core := core)) (scalar_le (core := core)) (Layout.prod_le' _ _ _ (wrapper.gammaOut_le' outLe) (xiIn_le (core := core))))
    (finalInput_le' (core := core)) (message_le (core := core))
    (Layout.prod_le' _ _ _ (scalar_le (core := core)) (Layout.prod_le' _ _ _ (wrapper.gammaOut_le' outLe) (xiIn_le (core := core))))).mono ?_ ?_
  all_goals simp only [finishTime, finishWords]; budget
theorem finish_names : NamesAccounted (wrapper.finish outLe routines).program.code S :=
  Implementation.pair'_names _ _ _ _ _ _ _ ((inForgery_names routines).seq (fMessage_names routines))
    (Implementation.pair'_names _ _ _ _ _ _ _ ((inForgery_names routines).seq (fBeta_names routines))
      (Implementation.pair'_names _ _ _ _ _ _ _ (wrapper.gammaFinal_names outLe routines)
        ((inForgery_names routines).seq (fXi_names routines))))

end Wrapper

end Signatures.Runtime.CaliperBackend.SyncWrap
