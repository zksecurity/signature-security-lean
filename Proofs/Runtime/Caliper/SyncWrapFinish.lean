import Proofs.Runtime.Caliper.SyncWrapPost
import Proofs.Runtime.Caliper.ListIndexBounds
import Proofs.Runtime.Caliper.ListFixedCons
import Proofs.Runtime.Caliper.ListReverseBounds
import Proofs.Runtime.Caliper.GuardedBranchBounds
import Proofs.Runtime.Caliper.ScalarBounds
import Proofs.Runtime.Caliper.FixedFoldBudgets
import Proofs.Runtime.Caliper.StructuralNames
import Proofs.Runtime.Caliper.StatefulCacheBuffers

/-! The wrapped forgery. The slots are folded in order: an attacker hash slot takes the next
coefficient of the inner forgery's hash list, a signing slot the next signing coefficient times
its correction; the final hash gets minus the finishing scalar. Positions are tracked by
saturating down-counters so every layout is fixed, and the output list is built by consing
and reversed. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull

set_option linter.unusedSectionVars false

variable {w : Nat} {Atom : Type} {base : Atom → Type} {key scalar : Ty Atom} {M G PK A : Type} [Zero (scalar.Value base)]
  {core : Core w (key.Value base) M G (scalar.Value base) PK A}

/-- The scalar type. -/
local notation "F" => scalar.Value base

namespace Wrapper

/-! ## Layouts of the inner coefficient lists -/
section Inner
abbrev gammaIn : Layout w (List F) := core.inner.good.extraction.gamma
abbrev xiIn : Layout w (List F) := core.inner.good.extraction.xi
abbrev capG : Nat := core.inner.scheme.gamma
abbrev capX : Nat := core.inner.scheme.xi

theorem gammaIn_words : (gammaIn (core := core)).representation.encoding.words = 1 + capG (core := core) * core.scalar.representation.encoding.words := rfl
theorem xiIn_words : (xiIn (core := core)).representation.encoding.words = 1 + capX (core := core) * core.scalar.representation.encoding.words := rfl
theorem forgeryIn_words : core.forgeryIn.representation.encoding.words =
    core.message.representation.encoding.words + (core.scalar.representation.encoding.words +
      ((gammaIn (core := core)).representation.encoding.words + (xiIn (core := core)).representation.encoding.words)) := rfl
theorem gammaIn_le : (gammaIn (core := core)).representation.encoding.words ≤ core.bound := by
  have := forgeryIn_words (core := core); unfold Core.bound Core.width; omega
theorem xiIn_le : (xiIn (core := core)).representation.encoding.words ≤ core.bound := by
  have := forgeryIn_words (core := core); unfold Core.bound Core.width; omega
theorem capG_lt : capG (core := core) < 2 ^ w := core.inner.scheme.goodBounds.gammaCount
theorem capX_lt : capX (core := core) < 2 ^ w := core.inner.scheme.goodBounds.xiCount

/-- Down-counters over the inner lists' positions. -/
abbrev counterG : Layout w Nat := Layout.counter w (capG (core := core) + 1) (width_pos core.wordFits) (capG_lt (core := core))
abbrev counterX : Layout w Nat := Layout.counter w (capX (core := core) + 1) (width_pos core.wordFits) (capX_lt (core := core))
theorem counterG_words : (counterG (core := core)).representation.encoding.words = 1 := rfl
theorem counterX_words : (counterX (core := core)).representation.encoding.words = 1 := rfl
include core in
theorem two_fits : 1 + 1 < 2 ^ w := by have := core.wordFits; omega
abbrev counters : Layout w (Nat × Nat) := (counterG (core := core)).prod (counterX (core := core)) (two_fits (core := core))
theorem counters_words : (counters (core := core)).representation.encoding.words = 2 := rfl

theorem envFits : (gammaIn (core := core)).representation.encoding.words + (xiIn (core := core)).representation.encoding.words < 2 ^ w := by
  have := gammaIn_le (core := core); have := xiIn_le (core := core); have := core.width_pos'
  exact core.fits (by unfold Core.bound at *; omega)
/-- The fold environment: the inner forgery's coefficient lists. -/
abbrev foldEnv : Layout w (List F × List F) := (gammaIn (core := core)).prod (xiIn (core := core)) (envFits (core := core))
theorem foldEnv_le : (foldEnv (core := core)).representation.encoding.words ≤ 2 * core.bound := by
  change (gammaIn (core := core)).representation.encoding.words + (xiIn (core := core)).representation.encoding.words ≤ _
  have := gammaIn_le (core := core); have := xiIn_le (core := core); omega

/-! ### Indexing the inner lists -/
/-- Executed indexing into a coefficient list. -/
def indexLayout (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storage : 8 * (3 + (capacity + 1) * core.scalar.representation.encoding.words) < 2 ^ w) : ListIndex.Layouts w (scalar.Value base) where
  value := core.scalar
  capacity := capacity
  indexBound := capacity + 1
  indexPositive := by omega
  indexFits := by omega
  wordFits := core.wordFits
  countFits := countFits
  storageFits := storage

theorem indexG_storage : 8 * (3 + (capG (core := core) + 1) * core.scalar.representation.encoding.words) < 2 ^ w := by
  have := gammaIn_words (core := core); have := gammaIn_le (core := core); have := core.scalarAll_le; have := core.scalarAll_words; have := core.width_pos'
  rw [Nat.add_mul, one_mul]; exact core.fits (by unfold Core.bound at *; omega)
theorem indexX_storage : 8 * (3 + (capX (core := core) + 1) * core.scalar.representation.encoding.words) < 2 ^ w := by
  have := xiIn_words (core := core); have := xiIn_le (core := core); have := core.scalarAll_le; have := core.scalarAll_words; have := core.width_pos'
  rw [Nat.add_mul, one_mul]; exact core.fits (by unfold Core.bound at *; omega)
abbrev indexG : ListIndex.Layouts w (scalar.Value base) := indexLayout (core := core) (capG (core := core)) (capG_lt (core := core)) indexG_storage
abbrev indexX : ListIndex.Layouts w (scalar.Value base) := indexLayout (core := core) (capX (core := core)) (capX_lt (core := core)) indexX_storage
theorem indexG_list : (indexG (core := core)).list = gammaIn (core := core) := rfl
theorem indexX_list : (indexX (core := core)).list = xiIn (core := core) := rfl
theorem indexG_counter : (indexG (core := core)).counter = counterG (core := core) := rfl
theorem indexX_counter : (indexX (core := core)).counter = counterX (core := core) := rfl
end Inner

/-! ## Layouts of the output list and the fold -/
section Outer
variable (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)

abbrev gammaOut : Layout w (List F) := wrapper.outer.good.extraction.gamma
abbrev capOut : Nat := wrapper.caps.gamma
theorem gammaOut_words : wrapper.gammaOut.representation.encoding.words = 1 + wrapper.capOut * core.scalar.representation.encoding.words := rfl
theorem forgeryOut_words : wrapper.outer.good.forgery.representation.encoding.words =
    core.message.representation.encoding.words + (core.scalar.representation.encoding.words +
      (wrapper.gammaOut.representation.encoding.words + (xiIn (core := core)).representation.encoding.words)) := rfl
theorem capOut_lt : wrapper.capOut < 2 ^ w := wrapper.caps.goodBounds.gammaCount
theorem capOut_eq : wrapper.capOut = wrapper.caps.gammaPred + 1 := rfl
include outLe in
theorem gammaOut_le : wrapper.gammaOut.representation.encoding.words ≤ core.bound := by
  have := wrapper.forgeryOut_words; unfold Core.bound Core.width; omega

include outLe in
theorem stateFits : (counters (core := core)).representation.encoding.words + wrapper.gammaOut.representation.encoding.words < 2 ^ w := by
  rw [counters_words]; have := wrapper.gammaOut_le outLe; have := core.width_pos'; exact core.fits (by unfold Core.bound at *; omega)
/-- The fold state: the counters beside the output list under construction. -/
abbrev foldState : Layout w ((Nat × Nat) × List F) := (counters (core := core)).prod wrapper.gammaOut (wrapper.stateFits outLe)
include outLe in
theorem foldState_le : (wrapper.foldState outLe).representation.encoding.words ≤ 2 + core.bound := by
  change 2 + wrapper.gammaOut.representation.encoding.words ≤ _; have := wrapper.gammaOut_le outLe; omega

include outLe in
theorem argFits : core.slotEntry.representation.encoding.words + (wrapper.foldState outLe).representation.encoding.words +
    (foldEnv (core := core)).representation.encoding.words < 2 ^ w := by
  have := core.slotEntry_le; have := wrapper.foldState_le outLe; have := foldEnv_le (core := core); have := core.width_pos'
  exact core.fits (by unfold Core.bound at *; omega)
include outLe in
theorem slots_words' : core.slots.representation.encoding.words = 1 + core.slotCap * core.slotEntry.representation.encoding.words := rfl
theorem frameFits : 1 + core.slotCap * core.slotEntry.representation.encoding.words + (wrapper.foldState outLe).representation.encoding.words +
    2 * (foldEnv (core := core)).representation.encoding.words < 2 ^ w := by
  have h1 : core.slotCap * core.slotEntry.representation.encoding.words ≤ core.bound := (Nat.le_add_left _ 1).trans core.slots_le
  have := core.width_pos'
  have := wrapper.foldState_le outLe; have := foldEnv_le (core := core); exact core.fits (by unfold Core.bound at *; omega)

/-- The fold body's input and the whole fold's input. -/
abbrev bodyInput := FoldImplementation.bodyInput core.slotEntry (wrapper.foldState outLe) (foldEnv (core := core)) (wrapper.argFits outLe)
abbrev foldInput := FoldImplementation.input core.slotEntry (wrapper.foldState outLe) (foldEnv (core := core)) core.slotCap
  (by have := core.slotCap_fits; omega) (wrapper.frameFits outLe)
end Outer

/-! ## Routines -/
/-- The finishing scalar, negation and multiplication, with their certificates. -/
structure FinishRoutines (core : Core w (key.Value base) M G (scalar.Value base) PK A) where
  finFn : F × M → F
  fin : Implementation .unit (core.scalar.prod core.message (core.fits2 (core.le3 core.scalarAll_le) (core.le3 core.messageAll_le))) core.scalar finFn
  negFn : F → F
  neg : Implementation .unit core.scalar core.scalar negFn
  mulFn : F × F → F
  mul : Implementation .unit (core.scalar.prod core.scalar (core.fits2 (core.le3 core.scalarAll_le) (core.le3 core.scalarAll_le))) core.scalar mulFn
  slots : Nat
  reserve : slots + 50 < 2 ^ w
  finBuffers : fin.program.code.memBound ≤ slots
  negBuffers : neg.program.code.memBound ≤ slots
  mulBuffers : mul.program.code.memBound ≤ slots
  time : Nat
  words : Nat
  finBound : fin.BoundedBy time words
  negBound : neg.BoundedBy time words
  mulBound : mul.BoundedBy time words
  finNames : NamesAccounted fin.program.code slots
  negNames : NamesAccounted neg.program.code slots
  mulNames : NamesAccounted mul.program.code slots

/-! ## The fold body -/
section Body
variable (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)
  (routines : FinishRoutines core)

/-- Every layout here is a small multiple of the bound. -/
theorem fitsBig {n : Nat} (h : n ≤ 40 * core.bound) : n < 2 ^ w := core.fits (by unfold Core.bound at h; have := core.width_pos'; omega)

theorem bound_pos : 17 ≤ core.bound := by unfold Core.bound; have := core.width_pos'; omega

set_option hygiene false in
/-- Close a storage bound after flattening products to base layouts. -/
scoped macro "fits_big" : tactic => `(tactic| (
  refine fitsBig (core := core) ?_
  have := wrapper.gammaOut_le outLe; have := scalar_le (core := core); have := message_le (core := core)
  have := gammaIn_le (core := core); have := xiIn_le (core := core); have := bound_pos (core := core)
  have hu : (DataImplementation.unitLayout w).representation.encoding.words = 0 := rfl
  simp only [Layout.prod_words, counters_words, counterG_words, counterX_words, counterOut_words, Layout.restrict_words] at *
  omega))

include outLe in
theorem restFits : (wrapper.foldState outLe).representation.encoding.words + (foldEnv (core := core)).representation.encoding.words < 2 ^ w :=
  fitsBig (core := core) (by have := wrapper.foldState_le outLe; have := foldEnv_le (core := core); have := bound_pos (core := core); omega)
/-- The fold state beside the environment. -/
abbrev rest : Layout w (((Nat × Nat) × List F) × (List F × List F)) := (wrapper.foldState outLe).prod (foldEnv (core := core)) (wrapper.restFits outLe)
include outLe in
theorem rest_le : (wrapper.rest outLe).representation.encoding.words ≤ 4 * core.bound := by
  change (wrapper.foldState outLe).representation.encoding.words + (foldEnv (core := core)).representation.encoding.words ≤ _
  have := wrapper.foldState_le outLe; have := foldEnv_le (core := core); have := bound_pos (core := core); omega
theorem counters_le : (counters (core := core)).representation.encoding.words ≤ core.bound := by rw [counters_words]; have := bound_pos (core := core); omega
theorem counterG_le : (counterG (core := core)).representation.encoding.words ≤ core.bound := by rw [counterG_words]; have := bound_pos (core := core); omega
theorem counterX_le : (counterX (core := core)).representation.encoding.words ≤ core.bound := by rw [counterX_words]; have := bound_pos (core := core); omega
theorem scalar_le : core.scalar.representation.encoding.words ≤ core.bound := by have := core.scalarAll_le; have := core.scalarAll_words; omega
theorem message_le : core.message.representation.encoding.words ≤ core.bound := by have := core.messageAll_le; have := core.messageAll_words; omega

/-! ### Projections from the state and environment -/
def restState : Implementation .unit (wrapper.rest outLe) (wrapper.foldState outLe) Prod.fst :=
  Implementation.first (by decide) _ _ core.wordFits (wrapper.restFits outLe)
def restEnv : Implementation .unit (wrapper.rest outLe) (foldEnv (core := core)) Prod.snd :=
  Implementation.second (by decide) _ _ core.wordFits (wrapper.restFits outLe)
def restCounters : Implementation .unit (wrapper.rest outLe) (counters (core := core)) (fun value => value.1.1) :=
  (wrapper.restState outLe).then (Implementation.first (by decide) _ _ core.wordFits (wrapper.stateFits outLe))
def restAcc : Implementation .unit (wrapper.rest outLe) wrapper.gammaOut (fun value => value.1.2) :=
  (wrapper.restState outLe).then (Implementation.second (by decide) _ _ core.wordFits (wrapper.stateFits outLe))
def restRi : Implementation .unit (wrapper.rest outLe) (counterG (core := core)) (fun value => value.1.1.1) :=
  (wrapper.restCounters outLe).then (Implementation.first (by decide) _ _ core.wordFits (two_fits (core := core)))
def restRj : Implementation .unit (wrapper.rest outLe) (counterX (core := core)) (fun value => value.1.1.2) :=
  (wrapper.restCounters outLe).then (Implementation.second (by decide) _ _ core.wordFits (two_fits (core := core)))
def restGamma : Implementation .unit (wrapper.rest outLe) (gammaIn (core := core)) (fun value => value.2.1) :=
  (wrapper.restEnv outLe).then (Implementation.first (by decide) _ _ core.wordFits (envFits (core := core)))
def restXi : Implementation .unit (wrapper.rest outLe) (xiIn (core := core)) (fun value => value.2.2) :=
  (wrapper.restEnv outLe).then (Implementation.second (by decide) _ _ core.wordFits (envFits (core := core)))

theorem restState_buffers : (wrapper.restState outLe).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem restEnv_buffers : (wrapper.restEnv outLe).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem restCounters_buffers : (wrapper.restCounters outLe).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (wrapper.restState_buffers outLe) (Implementation.first_buffers _ _ _ _ _)).trans (by omega)
theorem restAcc_buffers : (wrapper.restAcc outLe).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (wrapper.restState_buffers outLe) (Implementation.second_buffers _ _ _ _ _)).trans (by omega)
theorem restRi_buffers : (wrapper.restRi outLe).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (wrapper.restCounters_buffers outLe) (Implementation.first_buffers _ _ _ _ _)).trans (by omega)
theorem restRj_buffers : (wrapper.restRj outLe).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (wrapper.restCounters_buffers outLe) (Implementation.second_buffers _ _ _ _ _)).trans (by omega)
theorem restGamma_buffers : (wrapper.restGamma outLe).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (wrapper.restEnv_buffers outLe) (Implementation.first_buffers _ _ _ _ _)).trans (by omega)
theorem restXi_buffers : (wrapper.restXi outLe).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (wrapper.restEnv_buffers outLe) (Implementation.second_buffers _ _ _ _ _)).trans (by omega)

/-! ### Positions -/
include core in
theorem two_le : 2 ≤ 2 ^ w := by have := core.wordFits; omega
/-- The capacity, as a counter. -/
def capGConst : Implementation .unit (wrapper.rest outLe) (counterG (core := core)) (fun _ => capG (core := core)) :=
  Natural.constant .unit (by decide) _ (capG (core := core) + 1) (capG (core := core)) core.wordFits (capG_lt (core := core)) (Nat.lt_succ_self _)
def capXConst : Implementation .unit (wrapper.rest outLe) (counterX (core := core)) (fun _ => capX (core := core)) :=
  Natural.constant .unit (by decide) _ (capX (core := core) + 1) (capX (core := core)) core.wordFits (capX_lt (core := core)) (Nat.lt_succ_self _)
/-- One, as a counter below two. -/
def oneConst : Implementation .unit (wrapper.rest outLe) (Layout.counter w 2 (width_pos core.wordFits) (two_le (core := core))) (fun _ => 1) :=
  Natural.constant .unit (by decide) _ 2 1 core.wordFits (two_le (core := core)) (by omega)

theorem constant_buffers' {X : Type} {input : Layout w X} (bound value : Nat) (hw : 16 < 2 ^ w) (boundFits : bound ≤ 2 ^ w)
    (valid : value < bound) :
    (Natural.constant .unit (by decide) input bound value hw boundFits valid).program.code.memBound ≤ 35 := by
  have names := (Natural.constant_names input bound value hw boundFits valid 0).buffers
  have words := (Natural.constant_boundedBy input bound value hw boundFits valid).code_le
  omega
theorem capGConst_buffers : (wrapper.capGConst outLe).program.code.memBound ≤ 35 := constant_buffers' _ _ _ _ _
theorem capXConst_buffers : (wrapper.capXConst outLe).program.code.memBound ≤ 35 := constant_buffers' _ _ _ _ _
theorem oneConst_buffers : (wrapper.oneConst outLe).program.code.memBound ≤ 35 := constant_buffers' _ _ _ _ _

theorem subtract_buffers (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    (Natural.subtract .unit left right hw leftFits rightFits).program.code.memBound ≤ 3 := by
  change (Saturating.code (w := w)).memBound ≤ 3
  simp [Saturating.code, WordBinary.load, WordBinary.finish, Stmt.memBound]

/-- The position read by the counter: the capacity minus the remaining count. -/
def indexOfG : Implementation .unit (wrapper.rest outLe) (counterG (core := core)) (fun value => capG (core := core) - value.1.1.1) :=
  ((wrapper.capGConst outLe).pair' (wrapper.restRi outLe) core.wordFits (wrapper.capGConst_buffers outLe) (wrapper.restRi_buffers outLe)
    (core.room (by omega)) (fitsBig (core := core) (by have := wrapper.rest_le outLe; have := counterG_le (core := core); omega))).then
    (Natural.subtract .unit (capG (core := core) + 1) (capG (core := core) + 1) core.wordFits (capG_lt (core := core)) (capG_lt (core := core)))
def indexOfX : Implementation .unit (wrapper.rest outLe) (counterX (core := core)) (fun value => capX (core := core) - value.1.1.2) :=
  ((wrapper.capXConst outLe).pair' (wrapper.restRj outLe) core.wordFits (wrapper.capXConst_buffers outLe) (wrapper.restRj_buffers outLe)
    (core.room (by omega)) (fitsBig (core := core) (by have := wrapper.rest_le outLe; have := counterX_le (core := core); omega))).then
    (Natural.subtract .unit (capX (core := core) + 1) (capX (core := core) + 1) core.wordFits (capX_lt (core := core)) (capX_lt (core := core)))
/-- The remaining count, decremented. -/
def decG : Implementation .unit (wrapper.rest outLe) (counterG (core := core)) (fun value => value.1.1.1 - 1) :=
  ((wrapper.restRi outLe).pair' (wrapper.oneConst outLe) core.wordFits (wrapper.restRi_buffers outLe) (wrapper.oneConst_buffers outLe)
    (core.room (by omega)) (fitsBig (core := core) (by
      have := wrapper.rest_le outLe; have := counterG_le (core := core); have := bound_pos (core := core)
      have e : (Layout.counter w 2 (width_pos core.wordFits) (two_le (core := core))).representation.encoding.words = 1 := rfl; omega))).then
    (Natural.subtract .unit (capG (core := core) + 1) 2 core.wordFits (capG_lt (core := core)) (two_le (core := core)))
def decX : Implementation .unit (wrapper.rest outLe) (counterX (core := core)) (fun value => value.1.1.2 - 1) :=
  ((wrapper.restRj outLe).pair' (wrapper.oneConst outLe) core.wordFits (wrapper.restRj_buffers outLe) (wrapper.oneConst_buffers outLe)
    (core.room (by omega)) (fitsBig (core := core) (by
      have := wrapper.rest_le outLe; have := counterX_le (core := core); have := bound_pos (core := core)
      have e : (Layout.counter w 2 (width_pos core.wordFits) (two_le (core := core))).representation.encoding.words = 1 := rfl; omega))).then
    (Natural.subtract .unit (capX (core := core) + 1) 2 core.wordFits (capX_lt (core := core)) (two_le (core := core)))

theorem indexOfG_buffers : (wrapper.indexOfG outLe).program.code.memBound ≤ 36 :=
  (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (subtract_buffers _ _ _ _ _)).trans (by omega)
theorem indexOfX_buffers : (wrapper.indexOfX outLe).program.code.memBound ≤ 36 :=
  (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (subtract_buffers _ _ _ _ _)).trans (by omega)
theorem decG_buffers : (wrapper.decG outLe).program.code.memBound ≤ 36 :=
  (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (subtract_buffers _ _ _ _ _)).trans (by omega)
theorem decX_buffers : (wrapper.decX outLe).program.code.memBound ≤ 36 :=
  (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (subtract_buffers _ _ _ _ _)).trans (by omega)

/-! ### Coefficients -/
/-- Zero, the default coefficient. -/
def zeroScalar : Implementation .unit (wrapper.rest outLe) core.scalar (fun _ => 0) :=
  Implementation.constant _ core.scalar ⟨0, core.inner.scheme.zeroValid⟩ core.wordFits
theorem zeroScalar_buffers : (wrapper.zeroScalar outLe).program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _

/-- The coefficient at the current position of the inner hash list. -/
def lookupG : Implementation .unit (wrapper.rest outLe) core.scalar
    (fun value => (value.2.1[capG (core := core) - value.1.1.1]?).getD 0) :=
  ((wrapper.indexOfG outLe).pair' ((wrapper.zeroScalar outLe).pair' (wrapper.restGamma outLe) core.wordFits (wrapper.zeroScalar_buffers outLe)
      (wrapper.restGamma_buffers outLe) (core.room (by omega))
      (fitsBig (core := core) (by have := wrapper.rest_le outLe; have := scalar_le (core := core); have := gammaIn_le (core := core); omega)))
    core.wordFits (wrapper.indexOfG_buffers outLe) (Implementation.pair'_buffers _ _ _ _ _ _ _) (core.room (by omega))
    (fitsBig (core := core) (by
      have := wrapper.rest_le outLe; have := scalar_le (core := core); have := gammaIn_le (core := core); have := counterG_le (core := core)
      change _ + _ + _ + (core.scalar.representation.encoding.words + (gammaIn (core := core)).representation.encoding.words) ≤ _; omega))).then
    (ListIndex.implementation (indexG (core := core)))
def lookupX : Implementation .unit (wrapper.rest outLe) core.scalar
    (fun value => (value.2.2[capX (core := core) - value.1.1.2]?).getD 0) :=
  ((wrapper.indexOfX outLe).pair' ((wrapper.zeroScalar outLe).pair' (wrapper.restXi outLe) core.wordFits (wrapper.zeroScalar_buffers outLe)
      (wrapper.restXi_buffers outLe) (core.room (by omega))
      (fitsBig (core := core) (by have := wrapper.rest_le outLe; have := scalar_le (core := core); have := xiIn_le (core := core); omega)))
    core.wordFits (wrapper.indexOfX_buffers outLe) (Implementation.pair'_buffers _ _ _ _ _ _ _) (core.room (by omega))
    (fitsBig (core := core) (by
      have := wrapper.rest_le outLe; have := scalar_le (core := core); have := xiIn_le (core := core); have := counterX_le (core := core)
      change _ + _ + _ + (core.scalar.representation.encoding.words + (xiIn (core := core)).representation.encoding.words) ≤ _; omega))).then
    (ListIndex.implementation (indexX (core := core)))
theorem lookupG_buffers : (wrapper.lookupG outLe).program.code.memBound ≤ 37 := by
  unfold lookupG
  exact (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (ListIndex.buffers (indexG (core := core)))).trans (by omega)
theorem lookupX_buffers : (wrapper.lookupX outLe).program.code.memBound ≤ 37 := by
  unfold lookupX
  exact (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (ListIndex.buffers (indexX (core := core)))).trans (by omega)

end Body

/-! ## Guarded cons onto the output list -/
section Cons
variable (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)

abbrev counterOut : Layout w Nat := Layout.counter w (wrapper.capOut + 1) (width_pos core.wordFits) wrapper.capOut_lt
theorem counterOut_words : wrapper.counterOut.representation.encoding.words = 1 := rfl

/-- The stored length, read from the list's first word. -/
def lengthOut : Implementation .unit wrapper.gammaOut wrapper.counterOut List.length where
  preserves _ valid := Nat.lt_succ_of_le valid.1
  program := selectSliceRealizer .unit (by decide) wrapper.gammaOut.representation wrapper.counterOut.representation _ 0 core.wordFits
    (by rw [gammaOut_words]; change 0 + 1 ≤ _; omega)
    (by
      intro value
      change (BitVec.ofNat w (value.val.attachWith _ _).length :: _).take 1 = [BitVec.ofNat w value.val.length]
      simp [List.length_attachWith])
theorem lengthOut_buffers : wrapper.lengthOut.program.code.memBound ≤ 2 := selectSlice_buffers _ _
def capOutConst : Implementation .unit wrapper.gammaOut wrapper.counterOut (fun _ => wrapper.capOut) :=
  Natural.constant .unit (by decide) _ (wrapper.capOut + 1) wrapper.capOut core.wordFits wrapper.capOut_lt (Nat.lt_succ_self _)
theorem capOutConst_buffers : wrapper.capOutConst.program.code.memBound ≤ 35 := constant_buffers' _ _ _ _ _
include outLe in
theorem counterOut_fits : wrapper.gammaOut.representation.encoding.words + wrapper.gammaOut.representation.encoding.words +
    wrapper.counterOut.representation.encoding.words + wrapper.counterOut.representation.encoding.words < 2 ^ w :=
  fitsBig (core := core) (by rw [counterOut_words]; have := wrapper.gammaOut_le outLe; have := bound_pos (core := core); omega)
/-- Whether one more coefficient fits. -/
def hasRoomOut : Implementation .unit wrapper.gammaOut (Layout.all (Representation.boolean w (width_pos core.wordFits)))
    (fun values => decide (values.length < wrapper.capOut)) :=
  (wrapper.lengthOut.pair' wrapper.capOutConst core.wordFits wrapper.lengthOut_buffers wrapper.capOutConst_buffers (core.room (by omega))
    (wrapper.counterOut_fits outLe)).then
    (Natural.less .unit (wrapper.capOut + 1) (wrapper.capOut + 1) core.wordFits wrapper.capOut_lt wrapper.capOut_lt)
theorem less_buffers' (left right : Nat) (hw : 16 < 2 ^ w) (leftFits : left ≤ 2 ^ w) (rightFits : right ≤ 2 ^ w) :
    (Natural.less .unit left right hw leftFits rightFits).program.code.memBound ≤ 1 := by
  change (WordBinary.code (w := w) .ult).memBound ≤ 1
  simp [WordBinary.code, WordBinary.load, WordBinary.finish, Stmt.memBound]
theorem hasRoomOut_buffers : (wrapper.hasRoomOut outLe).program.code.memBound ≤ 37 :=
  (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (less_buffers' _ _ _ _ _)).trans (by omega)

include outLe in
theorem consFits : core.scalar.representation.encoding.words + wrapper.gammaOut.representation.encoding.words < 2 ^ w :=
  fitsBig (core := core) (by have := wrapper.gammaOut_le outLe; have := scalar_le (core := core); omega)
/-- A coefficient beside the output list. -/
abbrev consInput : Layout w (F × List F) := core.scalar.prod wrapper.gammaOut (wrapper.consFits outLe)
include outLe in
theorem consInput_le : (wrapper.consInput outLe).representation.encoding.words ≤ 2 * core.bound := by
  change core.scalar.representation.encoding.words + wrapper.gammaOut.representation.encoding.words ≤ _
  have := wrapper.gammaOut_le outLe; have := scalar_le (core := core); omega
def roomTestOut : Implementation .unit (wrapper.consInput outLe) (Layout.all (Representation.boolean w (width_pos core.wordFits)))
    (fun value => decide (value.2.length < wrapper.capOut)) :=
  (Implementation.second (by decide) core.scalar wrapper.gammaOut core.wordFits (wrapper.consFits outLe)).then (wrapper.hasRoomOut outLe)
theorem roomTestOut_buffers : (wrapper.roomTestOut outLe).program.code.memBound ≤ 37 :=
  max_le ((Implementation.second_buffers _ _ _ _ _).trans (by omega)) (wrapper.hasRoomOut_buffers outLe)

/-- Cons when there is room, otherwise keep the list. -/
def consFn (value : F × List F) : List F := if value.2.length < wrapper.capOut then value.1 :: value.2 else value.2

include outLe in
theorem fixedFrameFits : 1 + (wrapper.caps.gammaPred + 2) * core.scalar.representation.encoding.words < 2 ^ w := by
  have hg : wrapper.gammaOut.representation.encoding.words = 1 + (wrapper.caps.gammaPred + 1) * core.scalar.representation.encoding.words := rfl
  have := wrapper.gammaOut_le outLe; have := scalar_le (core := core)
  have e : (wrapper.caps.gammaPred + 2) * core.scalar.representation.encoding.words =
      (wrapper.caps.gammaPred + 1) * core.scalar.representation.encoding.words + core.scalar.representation.encoding.words := by ring
  exact fitsBig (core := core) (by rw [e]; omega)

def consGuard : Implementation .unit (wrapper.consInput outLe) wrapper.gammaOut wrapper.consFn :=
  (GuardedBranch.implementation (hw := core.wordFits) (wrapper.roomTestOut outLe) (by decide)
    (by have := wrapper.roomTestOut_buffers outLe; have := core.room (n := 38) (by omega); change max 2 _ < 2 ^ w; omega)
    (by fits_big) (by fits_big)
    ((Implementation.view (input := GuardedBranch.yesInput (wrapper.consInput outLe) (fun value => decide (value.2.length < wrapper.capOut)))
      (output := ListData.fixedConsInput core.scalar wrapper.caps.gammaPred wrapper.capOut_lt (wrapper.fixedFrameFits outLe)) (width_pos core.wordFits)
      (fun _ valid => ⟨valid.1, Nat.lt_succ_iff.mp (of_decide_eq_true valid.2)⟩) (fun _ => rfl)).then
      (ListData.fixedCons .unit (by decide) core.scalar wrapper.caps.gammaPred core.wordFits wrapper.capOut_lt (wrapper.fixedFrameFits outLe)))
    ((Implementation.second (by decide) core.scalar wrapper.gammaOut core.wordFits (wrapper.consFits outLe)).restrictInput _)).castFunction (by
      funext value
      simp only [consFn, Function.comp_apply, decide_eq_true_eq, id])
theorem consGuard_buffers : (wrapper.consGuard outLe).program.code.memBound ≤ 40 := by
  unfold consGuard
  refine (Implementation.castFunction_buffers _ _ (GuardedBranch.implementation_buffers _ _ _ _ _ _ (wrapper.roomTestOut_buffers outLe)
    (Implementation.then_buffers _ _ (Implementation.view_buffers _ _ _) (ListData.fixedCons_buffers _ _ _ _ _ _ _))
    (Implementation.second_buffers (cost := .unit) (by decide) core.scalar wrapper.gammaOut core.wordFits (wrapper.consFits outLe)))).trans ?_
  omega
end Cons

/-! ## The body and the fold -/
section Fold
variable (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)
  (routines : FinishRoutines core)

include outLe in
theorem unitRestFits : (DataImplementation.unitLayout w).representation.encoding.words + (wrapper.rest outLe).representation.encoding.words < 2 ^ w :=
  fitsBig (core := core) (by have := wrapper.rest_le outLe; change 0 + _ ≤ _; omega)
include outLe in
theorem scalarRestFits : core.scalar.representation.encoding.words + (wrapper.rest outLe).representation.encoding.words < 2 ^ w :=
  fitsBig (core := core) (by have := wrapper.rest_le outLe; have := scalar_le (core := core); omega)
abbrev hashInput : Layout w (Unit × (((Nat × Nat) × List F) × (List F × List F))) :=
  (DataImplementation.unitLayout w).prod (wrapper.rest outLe) (wrapper.unitRestFits outLe)
abbrev signInput : Layout w (F × (((Nat × Nat) × List F) × (List F × List F))) := core.scalar.prod (wrapper.rest outLe) (wrapper.scalarRestFits outLe)
include outLe in
theorem hashInput_le : (wrapper.hashInput outLe).representation.encoding.words ≤ 4 * core.bound := by
  change 0 + (wrapper.rest outLe).representation.encoding.words ≤ _; have := wrapper.rest_le outLe; omega
include outLe in
theorem signInput_le : (wrapper.signInput outLe).representation.encoding.words ≤ 5 * core.bound := by
  change core.scalar.representation.encoding.words + (wrapper.rest outLe).representation.encoding.words ≤ _
  have := wrapper.rest_le outLe; have := scalar_le (core := core); omega

/-- The state's components from a hash slot's input. -/
def hashRest : Implementation .unit (wrapper.hashInput outLe) (wrapper.rest outLe) Prod.snd :=
  Implementation.second (by decide) _ _ core.wordFits (wrapper.unitRestFits outLe)
def signRest : Implementation .unit (wrapper.signInput outLe) (wrapper.rest outLe) Prod.snd :=
  Implementation.second (by decide) _ _ core.wordFits (wrapper.scalarRestFits outLe)
def signEntry : Implementation .unit (wrapper.signInput outLe) core.scalar Prod.fst :=
  Implementation.first (by decide) _ _ core.wordFits (wrapper.scalarRestFits outLe)
theorem hashRest_buffers : (wrapper.hashRest outLe).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem signRest_buffers : (wrapper.signRest outLe).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem signEntry_buffers : (wrapper.signEntry outLe).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _

/-- An attacker hash slot: the next inner hash coefficient. -/
def hashStep : Implementation .unit (wrapper.hashInput outLe) (wrapper.foldState outLe)
    (fun value => ((value.2.1.1.1 - 1, value.2.1.1.2),
      wrapper.consFn ((value.2.2.1[capG (core := core) - value.2.1.1.1]?).getD 0, value.2.1.2))) :=
  (((wrapper.hashRest outLe).then (wrapper.decG outLe)).pair' ((wrapper.hashRest outLe).then (wrapper.restRj outLe)) core.wordFits
    (Implementation.then_buffers _ _ (wrapper.hashRest_buffers outLe) (wrapper.decG_buffers outLe))
    (Implementation.then_buffers _ _ (wrapper.hashRest_buffers outLe) (wrapper.restRj_buffers outLe)) (core.room (by omega))
    (by fits_big)).pair'
    ((((wrapper.hashRest outLe).then (wrapper.lookupG outLe)).pair' ((wrapper.hashRest outLe).then (wrapper.restAcc outLe)) core.wordFits
      (Implementation.then_buffers _ _ (wrapper.hashRest_buffers outLe) (wrapper.lookupG_buffers outLe))
      (Implementation.then_buffers _ _ (wrapper.hashRest_buffers outLe) (wrapper.restAcc_buffers outLe)) (core.room (by omega))
      (by fits_big)).then
      (wrapper.consGuard outLe)) core.wordFits
    (Implementation.pair'_buffers _ _ _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (wrapper.consGuard_buffers outLe)) (core.room (by omega))
    (by fits_big)

/-- A signing slot: the next inner signing coefficient times the correction. -/
def signStep : Implementation .unit (wrapper.signInput outLe) (wrapper.foldState outLe)
    (fun value => ((value.2.1.1.1, value.2.1.1.2 - 1),
      wrapper.consFn (routines.mulFn ((value.2.2.2[capX (core := core) - value.2.1.1.2]?).getD 0, value.1), value.2.1.2))) :=
  (((wrapper.signRest outLe).then (wrapper.restRi outLe)).pair' ((wrapper.signRest outLe).then (wrapper.decX outLe)) core.wordFits
    (Implementation.then_buffers _ _ (wrapper.signRest_buffers outLe) (wrapper.restRi_buffers outLe))
    (Implementation.then_buffers _ _ (wrapper.signRest_buffers outLe) (wrapper.decX_buffers outLe)) (core.room (by omega))
    (by fits_big)).pair'
    ((((((wrapper.signRest outLe).then (wrapper.lookupX outLe)).pair' (wrapper.signEntry outLe) core.wordFits
        (Implementation.then_buffers _ _ (wrapper.signRest_buffers outLe) (wrapper.lookupX_buffers outLe)) (wrapper.signEntry_buffers outLe)
        (core.room (by omega))
        (by fits_big)).then routines.mul).pair'
      ((wrapper.signRest outLe).then (wrapper.restAcc outLe)) core.wordFits
      (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) routines.mulBuffers)
      (Implementation.then_buffers _ _ (wrapper.signRest_buffers outLe) (wrapper.restAcc_buffers outLe)) (by have := routines.reserve; omega)
      (by fits_big)).then
      (wrapper.consGuard outLe)) core.wordFits
    (Implementation.pair'_buffers _ _ _ _ _ _ _)
    (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) (wrapper.consGuard_buffers outLe)) (by have := routines.reserve; omega)
    (by fits_big)

theorem hashStep_buffers : (wrapper.hashStep outLe).program.code.memBound ≤ 44 :=
  (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)
theorem signStep_buffers : (wrapper.signStep outLe routines).program.code.memBound ≤ max routines.slots 44 + 4 :=
  (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)

/-- The fold body, as a function. -/
def bodyFn (value : (Unit ⊕ F) × (((Nat × Nat) × List F) × (List F × List F))) : (Nat × Nat) × List F :=
  match value.1 with
  | .inl _ => ((value.2.1.1.1 - 1, value.2.1.1.2), wrapper.consFn ((value.2.2.1[capG (core := core) - value.2.1.1.1]?).getD 0, value.2.1.2))
  | .inr c => ((value.2.1.1.1, value.2.1.1.2 - 1),
      wrapper.consFn (routines.mulFn ((value.2.2.2[capX (core := core) - value.2.1.1.2]?).getD 0, c), value.2.1.2))

include outLe in
theorem bodySumFits : 1 + max (DataImplementation.unitLayout w).representation.encoding.words core.scalar.representation.encoding.words +
    (wrapper.rest outLe).representation.encoding.words < 2 ^ w :=
  fitsBig (core := core) (by
    have := wrapper.rest_le outLe; have := scalar_le (core := core); have := bound_pos (core := core)
    have e : (DataImplementation.unitLayout w).representation.encoding.words = 0 := rfl; omega)

/-- The fold body. -/
def body : Implementation .unit (wrapper.bodyInput outLe) (wrapper.foldState outLe) (wrapper.bodyFn routines) :=
  ((Implementation.distribute (DataImplementation.unitLayout w) core.scalar (wrapper.rest outLe) core.wordFits (wrapper.bodySumFits outLe)).then
    ((wrapper.hashStep outLe).branch (wrapper.signStep outLe routines) (by decide) core.wordFits
      (by fits_big))).castFunction (by
    funext value
    rcases value with ⟨_ | c, rest⟩ <;> rfl)
/-- The executed sum distribution uses three buffers. -/
theorem distribute_buffers' {X Y Z : Type} (left : Layout w X) (right : Layout w Y) (saved : Layout w Z) (hw : 16 < 2 ^ w)
    (fits : 1 + max left.representation.encoding.words right.representation.encoding.words + saved.representation.encoding.words < 2 ^ w) :
    (Implementation.distribute left right saved hw fits).program.code.memBound ≤ 3 :=
  SumContext.buffers left.representation right.representation saved.representation hw fits
theorem body_buffers : (wrapper.body outLe routines).program.code.memBound ≤ max routines.slots 44 + 4 := by
  unfold body
  refine (Implementation.castFunction_buffers _ _ (Implementation.then_buffers _ _ (distribute_buffers' _ _ _ _ _)
    (Implementation.branch_buffers _ _ _ _ (wrapper.hashStep_buffers outLe) (wrapper.signStep_buffers outLe routines)))).trans ?_
  omega

/-- The fold over the slots. -/
def fold : Implementation .unit (wrapper.foldInput outLe) (wrapper.foldState outLe) (FoldImplementation.sourceFold (wrapper.bodyFn routines)) :=
  FoldImplementation.compile core.slotEntry (wrapper.foldState outLe) (foldEnv (core := core)) (wrapper.argFits outLe) (wrapper.body outLe routines)
    (by decide) core.wordFits
    ((wrapper.body outLe routines).savedBuffer_lt (wrapper.body_buffers outLe routines) (by have := routines.reserve; omega))
    core.slotCap (by have := core.slotCap_fits; omega) (wrapper.frameFits outLe)
end Fold

/-! ## The finish -/
section Finish
variable (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)
  (routines : FinishRoutines core)

abbrev tailIn : Layout w (F × (List F × List F)) := core.inner.good.extraction.forgeryTail
abbrev explIn : Layout w (List F × List F) := core.inner.good.extraction.explanations

theorem unall_buffers {X : Type} (layout : Layout w X) : (Implementation.unall (width_pos core.wordFits) layout).program.code.memBound ≤ 0 :=
  Implementation.recast_buffers _ _ _ _ _ _

/-! ### The inputs -/
def inForgery : Implementation .unit core.finalInput core.forgeryAll Prod.fst :=
  Implementation.first (by decide) _ _ core.wordFits (core.fits2 (core.le3 core.forgeryAll_le) (core.le3 core.keyed_le))
def inKeyed : Implementation .unit core.finalInput core.keyed Prod.snd :=
  Implementation.second (by decide) _ _ core.wordFits (core.fits2 (core.le3 core.forgeryAll_le) (core.le3 core.keyed_le))
def inD : Implementation .unit core.finalInput core.scalar (fun value => value.2.1.val) :=
  ((inKeyed (core := core)).then (Implementation.first (by decide) core.scalarAll core.slots core.wordFits core.keyed_fits)).then
    (Implementation.unall (width_pos core.wordFits) core.scalar)
def inSlots : Implementation .unit core.finalInput core.slots (fun value => value.2.2) :=
  (inKeyed (core := core)).then (Implementation.second (by decide) core.scalarAll core.slots core.wordFits core.keyed_fits)
theorem inForgery_buffers : (inForgery (core := core)).program.code.memBound ≤ 2 := Implementation.first_buffers _ _ _ _ _
theorem inKeyed_buffers : (inKeyed (core := core)).program.code.memBound ≤ 2 := Implementation.second_buffers _ _ _ _ _
theorem inD_buffers : (inD (core := core)).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (inKeyed_buffers (core := core)) (Implementation.first_buffers _ _ _ _ _))
    (unall_buffers (core := core) _)).trans (by omega)
theorem inSlots_buffers : (inSlots (core := core)).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (inKeyed_buffers (core := core)) (Implementation.second_buffers _ _ _ _ _)).trans (by omega)

/-! ### The inner forgery's components -/
def fMessage : Implementation .unit core.forgeryAll core.message (fun value => value.val.1) :=
  core.forgeryMessage.then (Implementation.unall (width_pos core.wordFits) core.message)
def fTail : Implementation .unit core.forgeryAll (Layout.all (tailIn (core := core)).representation) (fun value => ⟨value.val.2, value.property.2⟩) :=
  Implementation.allSecond core.message (tailIn (core := core)) core.wordFits core.forgeryIn.representation.fits
def fBeta : Implementation .unit core.forgeryAll core.scalar (fun value => value.val.2.1) :=
  ((fTail (core := core)).then (Implementation.allFirst core.scalar (explIn (core := core)) core.wordFits (tailIn (core := core)).representation.fits)).then
    (Implementation.unall (width_pos core.wordFits) core.scalar)
def fExpl : Implementation .unit core.forgeryAll (Layout.all (explIn (core := core)).representation)
    (fun value => ⟨value.val.2.2, value.property.2.2⟩) :=
  (fTail (core := core)).then (Implementation.allSecond core.scalar (explIn (core := core)) core.wordFits (tailIn (core := core)).representation.fits)
def fGamma : Implementation .unit core.forgeryAll (gammaIn (core := core)) (fun value => value.val.2.2.1) :=
  ((fExpl (core := core)).then (Implementation.allFirst (gammaIn (core := core)) (xiIn (core := core)) core.wordFits (explIn (core := core)).representation.fits)).then
    (Implementation.unall (width_pos core.wordFits) (gammaIn (core := core)))
def fXi : Implementation .unit core.forgeryAll (xiIn (core := core)) (fun value => value.val.2.2.2) :=
  ((fExpl (core := core)).then (Implementation.allSecond (gammaIn (core := core)) (xiIn (core := core)) core.wordFits (explIn (core := core)).representation.fits)).then
    (Implementation.unall (width_pos core.wordFits) (xiIn (core := core)))
theorem fMessage_buffers : (fMessage (core := core)).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ core.forgeryMessage_buffers (unall_buffers (core := core) _)).trans (by omega)
theorem fTail_buffers : (fTail (core := core)).program.code.memBound ≤ 2 := Implementation.allSecond_buffers _ _ _ _
theorem fBeta_buffers : (fBeta (core := core)).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (fTail_buffers (core := core)) (Implementation.allFirst_buffers _ _ _ _))
    (unall_buffers (core := core) _)).trans (by omega)
theorem fExpl_buffers : (fExpl (core := core)).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (fTail_buffers (core := core)) (Implementation.allSecond_buffers _ _ _ _)).trans (by omega)
theorem fGamma_buffers : (fGamma (core := core)).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (fExpl_buffers (core := core)) (Implementation.allFirst_buffers _ _ _ _))
    (unall_buffers (core := core) _)).trans (by omega)
theorem fXi_buffers : (fXi (core := core)).program.code.memBound ≤ 2 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (fExpl_buffers (core := core)) (Implementation.allSecond_buffers _ _ _ _))
    (unall_buffers (core := core) _)).trans (by omega)

/-! ### The fold's input -/
theorem finalInput_le' : core.finalInput.representation.encoding.words ≤ 2 * core.bound := core.finalInput_le
def capGConst' : Implementation .unit core.finalInput (counterG (core := core)) (fun _ => capG (core := core)) :=
  Natural.constant .unit (by decide) _ (capG (core := core) + 1) (capG (core := core)) core.wordFits (capG_lt (core := core)) (Nat.lt_succ_self _)
def capXConst' : Implementation .unit core.finalInput (counterX (core := core)) (fun _ => capX (core := core)) :=
  Natural.constant .unit (by decide) _ (capX (core := core) + 1) (capX (core := core)) core.wordFits (capX_lt (core := core)) (Nat.lt_succ_self _)
def emptyOut : Implementation .unit core.finalInput wrapper.gammaOut (fun _ => []) :=
  Implementation.constant _ wrapper.gammaOut ⟨[], Nat.zero_le _, fun _ h => nomatch h⟩ core.wordFits
theorem capGConst'_buffers : (capGConst' (core := core)).program.code.memBound ≤ 35 := constant_buffers' _ _ _ _ _
theorem capXConst'_buffers : (capXConst' (core := core)).program.code.memBound ≤ 35 := constant_buffers' _ _ _ _ _
theorem emptyOut_buffers : wrapper.emptyOut.program.code.memBound ≤ 2 := Implementation.constant_buffers _ _ _ _

set_option hygiene false in
/-- Storage bounds over the finish input. -/
scoped macro "fits_fin" : tactic => `(tactic| (
  refine fitsBig (core := core) ?_
  have := wrapper.gammaOut_le outLe; have := scalar_le (core := core); have := message_le (core := core)
  have := gammaIn_le (core := core); have := xiIn_le (core := core); have := bound_pos (core := core)
  have := finalInput_le' (core := core); have := core.forgeryAll_le; have := core.keyed_le; have := core.slots_le
  have := core.scalarAll_words; have := core.messageAll_words
  simp only [Layout.prod_words, counters_words, counterG_words, counterX_words, counterOut_words] at *
  omega))

def initState : Implementation .unit core.finalInput (wrapper.foldState outLe) (fun _ => ((capG (core := core), capX (core := core)), [])) :=
  ((capGConst' (core := core)).pair' (capXConst' (core := core)) core.wordFits (capGConst'_buffers (core := core)) (capXConst'_buffers (core := core))
    (core.room (by omega)) (by fits_fin)).pair' wrapper.emptyOut core.wordFits (Implementation.pair'_buffers _ _ _ _ _ _ _) wrapper.emptyOut_buffers
    (core.room (by omega)) (by fits_fin)
def initEnv : Implementation .unit core.finalInput (foldEnv (core := core)) (fun value => (value.1.val.2.2.1, value.1.val.2.2.2)) :=
  ((inForgery (core := core)).then (fGamma (core := core))).pair' ((inForgery (core := core)).then (fXi (core := core))) core.wordFits
    (Implementation.then_buffers _ _ (inForgery_buffers (core := core)) (fGamma_buffers (core := core)))
    (Implementation.then_buffers _ _ (inForgery_buffers (core := core)) (fXi_buffers (core := core))) (core.room (by omega)) (by fits_fin)
theorem initState_buffers : (wrapper.initState outLe).program.code.memBound ≤ 37 := (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)
theorem initEnv_buffers : (wrapper.initEnv outLe).program.code.memBound ≤ 3 := (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)
/-- The fold's input from the finish input. -/
def prep : Implementation .unit core.finalInput (wrapper.foldInput outLe)
    (fun value => (value.2.2, (((capG (core := core), capX (core := core)), []), (value.1.val.2.2.1, value.1.val.2.2.2)))) :=
  (inSlots (core := core)).pair' ((wrapper.initState outLe).pair' (wrapper.initEnv outLe) core.wordFits (wrapper.initState_buffers outLe)
      (wrapper.initEnv_buffers outLe) (core.room (by omega)) (by fits_fin)) core.wordFits
    (inSlots_buffers (core := core)) (Implementation.pair'_buffers _ _ _ _ _ _ _) (core.room (by omega)) (by fits_fin)
theorem prep_buffers : (wrapper.prep outLe).program.code.memBound ≤ 39 := (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)

/-- The fold's output list. -/
def accOut : Implementation .unit core.finalInput wrapper.gammaOut
    (fun value => (FoldImplementation.sourceFold (wrapper.bodyFn routines)
      (value.2.2, (((capG (core := core), capX (core := core)), []), (value.1.val.2.2.1, value.1.val.2.2.2)))).2) :=
  ((wrapper.prep outLe).then (wrapper.fold outLe routines)).then (Implementation.second (by decide) _ _ core.wordFits (wrapper.stateFits outLe))
theorem fold_buffers : (wrapper.fold outLe routines).program.code.memBound ≤ max routines.slots 44 + 5 :=
  (ListFold.buffers (wrapper.body outLe routines).program.code _ _ _ _).trans (by have := wrapper.body_buffers outLe routines; omega)
theorem accOut_buffers : (wrapper.accOut outLe routines).program.code.memBound ≤ max routines.slots 44 + 5 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (wrapper.prep_buffers outLe) (wrapper.fold_buffers outLe routines))
    (Implementation.second_buffers _ _ _ _ _)).trans (by omega)

/-- Minus the finishing scalar. -/
def finScalar : Implementation .unit core.finalInput core.scalar (fun value => routines.negFn (routines.finFn (value.2.1.val, value.1.val.1))) :=
  (((inD (core := core)).pair' ((inForgery (core := core)).then (fMessage (core := core))) core.wordFits (inD_buffers (core := core))
    (Implementation.then_buffers _ _ (inForgery_buffers (core := core)) (fMessage_buffers (core := core))) (core.room (by omega)) (by fits_fin)).then
    routines.fin).then routines.neg
theorem finScalar_buffers : (wrapper.finScalar outLe routines).program.code.memBound ≤ max routines.slots 3 :=
  (Implementation.then_buffers _ _ (Implementation.then_buffers _ _ (Implementation.pair'_buffers _ _ _ _ _ _ _) routines.finBuffers)
    routines.negBuffers).trans (by omega)

/-- The output list as the executed reversal's layouts. -/
def revLayout : ListReverse.Layouts w (scalar.Value base) where
  entry := core.scalar
  capacity := wrapper.capOut
  wordFits := core.wordFits
  countFits := wrapper.capOut_lt
  storageFits := by
    have := wrapper.gammaOut_words; have := wrapper.gammaOut_le outLe; have := scalar_le (core := core)
    have e : (wrapper.capOut + 1) * core.scalar.representation.encoding.words =
        wrapper.capOut * core.scalar.representation.encoding.words + core.scalar.representation.encoding.words := by ring
    exact fitsBig (core := core) (by rw [e]; omega)
theorem revLayout_list : (wrapper.revLayout outLe).list = wrapper.gammaOut := rfl

theorem room' {n : Nat} (small : n ≤ 100) : max routines.slots n + 2 < 2 ^ w := by
  have := routines.reserve; have := core.room (n := 100) le_rfl; omega

/-- The finishing scalar beside the folded list. -/
def consFinal : Implementation .unit core.finalInput (wrapper.consInput outLe)
    (fun value => (routines.negFn (routines.finFn (value.2.1.val, value.1.val.1)),
      (FoldImplementation.sourceFold (wrapper.bodyFn routines)
        (value.2.2, (((capG (core := core), capX (core := core)), []), (value.1.val.2.2.1, value.1.val.2.2.2)))).2)) :=
  (wrapper.finScalar outLe routines).pair' (wrapper.accOut outLe routines) core.wordFits (wrapper.finScalar_buffers outLe routines)
    (wrapper.accOut_buffers outLe routines) (by have := routines.reserve; have := core.room (n := 100) le_rfl; omega) (by fits_fin)
theorem consFinal_buffers : (wrapper.consFinal outLe routines).program.code.memBound ≤ max routines.slots 44 + 6 :=
  (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)
/-- The output list before reversal. -/
def consed : Implementation .unit core.finalInput wrapper.gammaOut
    (fun value => wrapper.consFn (routines.negFn (routines.finFn (value.2.1.val, value.1.val.1)),
      (FoldImplementation.sourceFold (wrapper.bodyFn routines)
        (value.2.2, (((capG (core := core), capX (core := core)), []), (value.1.val.2.2.1, value.1.val.2.2.2)))).2)) :=
  (wrapper.consFinal outLe routines).then (wrapper.consGuard outLe)
theorem consed_buffers : (wrapper.consed outLe routines).program.code.memBound ≤ max routines.slots 44 + 6 :=
  (Implementation.then_buffers _ _ (wrapper.consFinal_buffers outLe routines) (wrapper.consGuard_buffers outLe)).trans (by omega)
/-- The wrapped forgery's hash coefficients. -/
def reverseOut : Implementation .unit wrapper.gammaOut wrapper.gammaOut List.reverse := ListReverse.implementation (wrapper.revLayout outLe)
def gammaFinal : Implementation .unit core.finalInput wrapper.gammaOut
    (fun value => (wrapper.consFn (routines.negFn (routines.finFn (value.2.1.val, value.1.val.1)),
      (FoldImplementation.sourceFold (wrapper.bodyFn routines)
        (value.2.2, (((capG (core := core), capX (core := core)), []), (value.1.val.2.2.1, value.1.val.2.2.2)))).2)).reverse) :=
  (wrapper.consed outLe routines).then (wrapper.reverseOut outLe)
theorem reverseOut_buffers : (wrapper.reverseOut outLe).program.code.memBound ≤ 3 := ListReverse.buffers _
theorem gammaFinal_buffers : (wrapper.gammaFinal outLe routines).program.code.memBound ≤ max routines.slots 44 + 6 :=
  (Implementation.then_buffers _ _ (wrapper.consed_buffers outLe routines) (wrapper.reverseOut_buffers outLe)).trans (by omega)

/-- The wrapped forgery, as a function. -/
def finishFn (value : core.forgeryIn.Value × (core.scalar.Value × List (Unit ⊕ F))) : M × (F × (List F × List F)) :=
  (value.1.val.1, (value.1.val.2.1,
    ((wrapper.consFn (routines.negFn (routines.finFn (value.2.1.val, value.1.val.1)),
      (FoldImplementation.sourceFold (wrapper.bodyFn routines)
        (value.2.2, (((capG (core := core), capX (core := core)), []), (value.1.val.2.2.1, value.1.val.2.2.2)))).2)).reverse,
     value.1.val.2.2.2)))

/-- The wrapped forgery. -/
def finish : Implementation .unit core.finalInput wrapper.outer.good.forgery (wrapper.finishFn routines) :=
  ((inForgery (core := core)).then (fMessage (core := core))).pair'
    (((inForgery (core := core)).then (fBeta (core := core))).pair'
      ((wrapper.gammaFinal outLe routines).pair' ((inForgery (core := core)).then (fXi (core := core))) core.wordFits
        (wrapper.gammaFinal_buffers outLe routines) (Implementation.then_buffers _ _ (inForgery_buffers (core := core)) (fXi_buffers (core := core)))
        (by have := routines.reserve; have := core.room (n := 100) le_rfl; omega) (by fits_fin))
      core.wordFits (Implementation.then_buffers _ _ (inForgery_buffers (core := core)) (fBeta_buffers (core := core)))
      (Implementation.pair'_buffers _ _ _ _ _ _ _) (by have := routines.reserve; have := core.room (n := 100) le_rfl; omega) (by fits_fin))
    core.wordFits (Implementation.then_buffers _ _ (inForgery_buffers (core := core)) (fMessage_buffers (core := core)))
    (Implementation.pair'_buffers _ _ _ _ _ _ _) (by have := routines.reserve; have := core.room (n := 100) le_rfl; omega) (by fits_fin)
theorem finish_buffers : (wrapper.finish outLe routines).program.code.memBound ≤ max routines.slots 44 + 9 :=
  (Implementation.pair'_buffers _ _ _ _ _ _ _).trans (by omega)
end Finish

/-! ## What the finish computes -/
section Semantics
variable (wrapper : Wrapper core) (outLe : wrapper.outer.good.forgery.representation.encoding.words ≤ core.outWords)
  (routines : FinishRoutines core) [Mul (scalar.Value base)] (mulLaw : ∀ a b, routines.mulFn (a, b) = a * b)

/-- The wrapper's hash coefficients from the slots: the inner hash coefficients in order on
the attacker's hash slots, the inner signing coefficients times the corrections on the
signing slots. -/
def remapMarks (γ ξ : List F) : List (Unit ⊕ F) → Nat → Nat → List F
  | [], _, _ => []
  | .inl _ :: rest, i, j => Model.LazyAGM.tokenCoeff γ i :: remapMarks γ ξ rest (i + 1) j
  | .inr c :: rest, i, j => Model.LazyAGM.tokenCoeff ξ j * c :: remapMarks γ ξ rest i (j + 1)

/-- The number of hash and of signing slots. -/
def hashCount : List (Unit ⊕ F) → Nat
  | [] => 0
  | .inl _ :: rest => hashCount rest + 1
  | .inr _ :: rest => hashCount rest
def signCount : List (Unit ⊕ F) → Nat
  | [] => 0
  | .inl _ :: rest => signCount rest
  | .inr _ :: rest => signCount rest + 1

omit [Mul (scalar.Value base)] in
/-- Reading at the saturated position is reading at the position: both miss past the list. -/
theorem tokenCoeff_saturate (γ : List F) (cap i : Nat) (h : γ.length ≤ cap) :
    (γ[cap - (cap - i)]?).getD 0 = Model.LazyAGM.tokenCoeff γ i := by
  unfold Model.LazyAGM.tokenCoeff
  by_cases hi : i ≤ cap
  · rw [Nat.sub_sub_self hi]
  · have h1 : cap - i = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [h1, Nat.sub_zero, List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

omit [Mul (scalar.Value base)] in
theorem consFn_of_lt (x : F) (acc : List F) (h : acc.length < wrapper.capOut) : wrapper.consFn (x, acc) = x :: acc := by
  simp [consFn, h]

include mulLaw in
/-- The fold over the slots, with its position counters and the room it needs. -/
theorem fold_eq (γ ξ : List F) (hγ : γ.length ≤ capG (core := core)) (hξ : ξ.length ≤ capX (core := core))
    (marks : List (Unit ⊕ F)) (i j : Nat) (acc : List F) (room : acc.length + marks.length < wrapper.capOut) :
    FoldImplementation.sourceFold (wrapper.bodyFn routines) (marks, (((capG (core := core) - i, capX (core := core) - j), acc), (γ, ξ))) =
      ((capG (core := core) - (i + hashCount marks), capX (core := core) - (j + signCount marks)), (remapMarks γ ξ marks i j).reverse ++ acc) := by
  induction marks generalizing i j acc with
  | nil => simp [FoldImplementation.sourceFold, remapMarks, hashCount, signCount]
  | cons head rest ih =>
    rcases head with _ | c
    · have step : FoldImplementation.sourceFold (wrapper.bodyFn routines) (Sum.inl () :: rest, (((capG (core := core) - i, capX (core := core) - j), acc), (γ, ξ))) =
          FoldImplementation.sourceFold (wrapper.bodyFn routines) (rest, (((capG (core := core) - (i + 1), capX (core := core) - j),
            Model.LazyAGM.tokenCoeff γ i :: acc), (γ, ξ))) := by
        simp only [FoldImplementation.sourceFold, List.foldl_cons, bodyFn]
        rw [wrapper.consFn_of_lt _ _ (by simp only [List.length_cons] at room; omega), Nat.sub_sub, tokenCoeff_saturate γ _ i hγ]
      rw [step, ih (i + 1) j _ (by simp only [List.length_cons] at room ⊢; omega)]
      simp [remapMarks, hashCount, signCount, Nat.add_assoc, Nat.add_comm 1]
    · have step : FoldImplementation.sourceFold (wrapper.bodyFn routines) (Sum.inr c :: rest, (((capG (core := core) - i, capX (core := core) - j), acc), (γ, ξ))) =
          FoldImplementation.sourceFold (wrapper.bodyFn routines) (rest, (((capG (core := core) - i, capX (core := core) - (j + 1)),
            Model.LazyAGM.tokenCoeff ξ j * c :: acc), (γ, ξ))) := by
        simp only [FoldImplementation.sourceFold, List.foldl_cons, bodyFn]
        rw [mulLaw, wrapper.consFn_of_lt _ _ (by simp only [List.length_cons] at room; omega), Nat.sub_sub, tokenCoeff_saturate ξ _ j hξ]
      rw [step, ih i (j + 1) _ (by simp only [List.length_cons] at room ⊢; omega)]
      simp [remapMarks, hashCount, signCount, Nat.add_assoc, Nat.add_comm 1]

include mulLaw in
/-- The wrapped forgery: the inner message and base coefficient, the remapped hash
coefficients followed by minus the finishing scalar, the inner signing coefficients. -/
theorem finishFn_eq (value : core.forgeryIn.Value × (core.scalar.Value × List (Unit ⊕ F))) (slotsLe : value.2.2.length ≤ core.slotCap) :
    wrapper.finishFn routines value = (value.1.val.1, (value.1.val.2.1,
      (remapMarks value.1.val.2.2.1 value.1.val.2.2.2 value.2.2 0 0 ++ [routines.negFn (routines.finFn (value.2.1.val, value.1.val.1))],
       value.1.val.2.2.2))) := by
  have hγ : value.1.val.2.2.1.length ≤ capG (core := core) := value.1.property.2.2.1.1
  have hξ : value.1.val.2.2.2.length ≤ capX (core := core) := value.1.property.2.2.2.1
  have room : wrapper.caps.gammaPred + 1 = wrapper.capOut := rfl
  have slotRoom := wrapper.gammaRoom
  unfold finishFn
  rw [show capG (core := core) = capG (core := core) - 0 from rfl, show capX (core := core) = capX (core := core) - 0 from rfl,
    wrapper.fold_eq routines mulLaw _ _ hγ hξ _ 0 0 [] (by simp; omega)]
  simp only [List.append_nil]
  rw [wrapper.consFn_of_lt _ _ (by rw [List.length_reverse]; have := remapMarks_length value.1.val.2.2.1 value.1.val.2.2.2 value.2.2 0 0; omega),
    List.reverse_cons, List.reverse_reverse]
where
  remapMarks_length (γ ξ : List F) : ∀ (marks : List (Unit ⊕ F)) (i j : Nat), (remapMarks γ ξ marks i j).length = marks.length
    | [], _, _ => rfl
    | .inl _ :: rest, i, j => by simp [remapMarks, remapMarks_length γ ξ rest]
    | .inr _ :: rest, i, j => by simp [remapMarks, remapMarks_length γ ξ rest]
end Semantics

end Wrapper

end Signatures.Runtime.CaliperBackend.SyncWrap
