import Proofs.Runtime.Caliper.SyncWrapLayout
import Proofs.Runtime.Caliper.ListSnocBounds
import Proofs.Runtime.Caliper.GuardedBranchBounds
import Proofs.Runtime.Caliper.ScalarBounds

/-! Appending a hash slot. The slot list has a fixed capacity, so the executed append first
reads the stored length and keeps the list unchanged when it is full; the caller invariant
rules the full case out on every reachable run. -/
namespace Signatures.Runtime.CaliperBackend.SyncWrap
open Caliper BoundedSource WeightedFull

variable {w : Nat} {K M G F PK A : Type} [Zero F] (core : Core w K M G F PK A)

namespace Core

theorem slotCap_fits : core.slotCap + 1 < 2 ^ w := core.fits (by unfold width; nlinarith)

/-- The stored length, read from the list's first word. -/
def counter : Layout w Nat := Layout.counter w (core.slotCap + 1) (width_pos core.wordFits) core.slotCap_fits.le

def lengthOf : Implementation .unit core.slots core.counter List.length where
  preserves _ valid := Nat.lt_succ_of_le valid.1
  program := selectSliceRealizer .unit (by decide) core.slots.representation core.counter.representation _ 0 core.wordFits
    (by rw [slots_words]; change 0 + 1 ≤ _; omega)
    (by
      intro value
      change (BitVec.ofNat w (value.val.attachWith _ _).length :: _).take 1 = [BitVec.ofNat w value.val.length]
      simp [List.length_attachWith])

theorem lengthOf_boundedBy : core.lengthOf.BoundedBy 14 40 := by
  constructor
  · intro _
    change (selectSlice (w := w) 0 1).staticTime .unit ≤ _
    simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
    omega
  · exact (selectSlice_descriptionWords 0 1).le
theorem lengthOf_names (slots : Nat) : NamesAccounted core.lengthOf.program.code slots := selectSlice_names _ _ _
theorem lengthOf_buffers : core.lengthOf.program.code.memBound ≤ 2 := selectSlice_buffers _ _

/-- The capacity, as a counter. -/
def capacity : Implementation .unit core.slots core.counter (fun _ => core.slotCap) :=
  Natural.constant .unit (by decide) core.slots (core.slotCap + 1) core.slotCap core.wordFits core.slotCap_fits.le (Nat.lt_succ_self _)

theorem counter_words : core.counter.representation.encoding.words = 1 := rfl
theorem capacity_buffers : core.capacity.program.code.memBound ≤ 35 := by
  have names := (Natural.constant_names core.slots (core.slotCap + 1) core.slotCap core.wordFits core.slotCap_fits.le (Nat.lt_succ_self _) 0).buffers
  have words := (Natural.constant_boundedBy core.slots (core.slotCap + 1) core.slotCap core.wordFits core.slotCap_fits.le (Nat.lt_succ_self _)).code_le
  unfold capacity
  omega

/-- Whether one more slot fits. -/
def hasRoom : Implementation .unit core.slots (Layout.all (Representation.boolean w (width_pos core.wordFits)))
    (fun values => decide (values.length < core.slotCap)) :=
  ((core.lengthOf.pair core.capacity (by decide) core.wordFits
    (by have := core.lengthOf_buffers; have := core.wordFits; change max 2 _ < 2 ^ w; omega)
    (by have := core.capacity_buffers; have := core.fits (n := 36) (by unfold width; omega); change max 2 _ < 2 ^ w; omega)
    (by rw [slots_words]; exact core.fits (by unfold width; omega))
    (by rw [slots_words, counter_words]; exact core.fits (by unfold width; omega))
    (by change 1 + 1 < 2 ^ w; have := core.wordFits; omega)).then
    (Natural.less .unit (core.slotCap + 1) (core.slotCap + 1) core.wordFits core.slotCap_fits.le core.slotCap_fits.le))


theorem less_boundedBy : (Natural.less .unit (core.slotCap + 1) (core.slotCap + 1) core.wordFits core.slotCap_fits.le core.slotCap_fits.le).BoundedBy 6 27 :=
  ⟨fun value => (Natural.less_time_unit _ _ _ _ _ value).le, (WordBinary.descriptionWords_eq .ult).le⟩
theorem less_names (slots : Nat) :
    NamesAccounted (Natural.less .unit (core.slotCap + 1) (core.slotCap + 1) core.wordFits core.slotCap_fits.le core.slotCap_fits.le).program.code slots := by
  change NamesAccounted (WordBinary.code (w := w) .ult) slots
  have registers : registerSlots (WordBinary.code (w := w) .ult) ≤ 3 := by
    simp [WordBinary.code, WordBinary.load, WordBinary.finish, registerSlots]
  have buffers : (WordBinary.code (w := w) .ult).memBound ≤ 1 := by
    simp [WordBinary.code, WordBinary.load, WordBinary.finish, Stmt.memBound]
  have words : descriptionWords (WordBinary.code (w := w) .ult) = 27 := WordBinary.descriptionWords_eq .ult
  constructor <;> omega
theorem less_buffers : (Natural.less .unit (core.slotCap + 1) (core.slotCap + 1) core.wordFits core.slotCap_fits.le core.slotCap_fits.le).program.code.memBound ≤ 1 := by
  change (WordBinary.code (w := w) .ult).memBound ≤ 1
  simp [WordBinary.code, WordBinary.load, WordBinary.finish, Stmt.memBound]

theorem hasRoom_boundedBy : core.hasRoom.BoundedBy (6 + 400 * core.width) (27 + 1300 * core.width + 300) := by
  unfold hasRoom
  apply ((Implementation.pair_boundedBy _ _ _ _ _ _ _ _ core.lengthOf_boundedBy
    (Natural.constant_boundedBy core.slots (core.slotCap + 1) core.slotCap core.wordFits core.slotCap_fits.le (Nat.lt_succ_self _))).then
      core.less_boundedBy).mono
  all_goals
    have := core.slots_words
    have := core.counter_words
    simp only [show ∀ h₁ h₂, (Layout.counter w (core.slotCap + 1) h₁ h₂).representation.encoding.words = 1 from fun _ _ => rfl]
    unfold width at *
    omega
theorem hasRoom_names (slots : Nat) : NamesAccounted core.hasRoom.program.code slots := by
  unfold hasRoom
  exact (Implementation.pair_names _ _ _ _ _ _ _ _ (core.lengthOf_names slots)
    (Natural.constant_names core.slots (core.slotCap + 1) core.slotCap core.wordFits core.slotCap_fits.le (Nat.lt_succ_self _) slots)).seq
    (core.less_names slots)
theorem hasRoom_buffers : core.hasRoom.program.code.memBound ≤ 37 := by
  unfold hasRoom
  change max _ _ ≤ 37
  exact max_le ((Implementation.pair_buffers _ _ _ _ _ _ _ _ core.lengthOf_buffers core.capacity_buffers).trans (by omega))
    (core.less_buffers.trans (by omega))

/-- The slot list as the executed append's layouts. -/
def snocLayout : ListSnoc.Layouts w (Unit ⊕ F) where
  entry := core.slotEntry
  capacity := core.slotCap
  wordFits := core.wordFits
  countFits := core.slotCap_fits
  storageFits := by rw [slotEntry_words]; exact core.fits (by unfold width; nlinarith)

theorem snocLayout_list : core.snocLayout.list = core.slots := rfl

/-- A slot beside the list. -/
def appendInput : Layout w ((Unit ⊕ F) × List (Unit ⊕ F)) := core.slotEntry.prod core.slots (by
  rw [slotEntry_words, slots_words]; exact core.fits (by unfold width; omega))
theorem appendInput_raw : core.appendInput = core.snocLayout.raw := rfl
theorem appendInput_words : core.appendInput.representation.encoding.words ≤ 2 + core.width := by
  change core.slotEntry.representation.encoding.words + core.slots.representation.encoding.words ≤ _
  rw [slotEntry_words, slots_words]; unfold width; omega

/-- Whether the list beside the slot has room. -/
def roomTest : Implementation .unit core.appendInput (Layout.all (Representation.boolean w (width_pos core.wordFits)))
    (fun value => decide (value.2.length < core.slotCap)) :=
  (Implementation.second (by decide) core.slotEntry core.slots core.wordFits _).then core.hasRoom

/-- Append a slot when there is room, otherwise keep the list. -/
def append (value : (Unit ⊕ F) × List (Unit ⊕ F)) : List (Unit ⊕ F) :=
  if value.2.length < core.slotCap then value.2 ++ [value.1] else value.2

theorem roomTest_buffers : core.roomTest.program.code.memBound ≤ 37 :=
  max_le ((Implementation.second_buffers _ _ _ _ _).trans (by omega)) core.hasRoom_buffers

def snoc : Implementation .unit core.appendInput core.slots core.append :=
  (GuardedBranch.implementation (hw := core.wordFits) core.roomTest (by decide)
    (by have := core.roomTest_buffers; have := core.fits (n := 38) (by unfold width; omega); change max 2 _ < 2 ^ w; omega)
    (by have := core.appendInput_words; exact core.fits (by unfold width at *; omega))
    (by have := core.appendInput_words; exact core.fits (by unfold width at *; omega))
    ((Implementation.view (input := GuardedBranch.yesInput core.appendInput (fun value => decide (value.2.length < core.slotCap)))
      (output := core.snocLayout.input) (width_pos core.wordFits)
      (fun _ valid => ⟨valid.1, of_decide_eq_true valid.2⟩) (fun _ => rfl)).then
      (ListSnoc.implementation core.snocLayout))
    ((Implementation.second (by decide) core.slotEntry core.slots core.wordFits _).restrictInput _)).castFunction (by
      funext value
      simp only [append, Function.comp_apply, decide_eq_true_eq, id])

end Core

namespace Core

theorem roomTest_boundedBy : core.roomTest.BoundedBy (6 + 420 * core.width) (27 + 1400 * core.width + 400) := by
  unfold roomTest
  apply ((Implementation.second_boundedBy _ _ _ _).then core.hasRoom_boundedBy).mono
  all_goals have := core.slots_words; have := core.appendInput_words; unfold width at *; omega
theorem roomTest_names (slots : Nat) : NamesAccounted core.roomTest.program.code slots :=
  (Implementation.second_names _ _ _ _ _).seq (core.hasRoom_names slots)

/-- Budgets of the guarded append. -/
def snocTime : Nat := 6 + 420 * core.width + ListSnoc.timeBudget core.snocLayout + 8 * (2 + core.width) + 76 * (2 + core.width) + 43
def snocWords : Nat := 27 + 1400 * core.width + 400 + ListSnoc.codeBudget core.snocLayout + 1 + 26 * (2 + core.width) + 14 +
  273 * (2 + core.width) + 304

theorem snoc_boundedBy : core.snoc.BoundedBy core.snocTime core.snocWords := by
  unfold snoc
  refine (Implementation.BoundedBy.castFunction (GuardedBranch.implementation_boundedBy _ _ _ _ _ _ core.roomTest_boundedBy
    ((Implementation.view_boundedBy _ _ _).then (ListSnoc.bounded core.snocLayout))
    ((Implementation.second_boundedBy _ _ _ _).restrictInput _)) _).mono ?_ ?_
  all_goals
    have := core.appendInput_words
    have e : core.snocLayout.list.representation.encoding.words = 1 + core.slotCap * (1 + core.scalar.representation.encoding.words) :=
      core.slots_words
    simp only [snocTime, snocWords]
    unfold width at *
    omega
theorem snoc_names (slots : Nat) : NamesAccounted core.snoc.program.code slots :=
  GuardedBranch.implementation_names _ _ _ _ _ _ (core.roomTest_names slots)
    ((Implementation.view_names _ _ _ slots).seq (ListSnoc.names core.snocLayout slots))
    (Implementation.second_names core.slotEntry core.slots core.wordFits
      (by rw [slotEntry_words, slots_words]; exact core.fits (by unfold width; omega)) slots)
theorem appendInput_fits : core.slotEntry.representation.encoding.words + core.slots.representation.encoding.words < 2 ^ w := by
  rw [slotEntry_words, slots_words]; exact core.fits (by unfold width; omega)
theorem snoc_buffers : core.snoc.program.code.memBound ≤ 40 := by
  unfold snoc
  refine (Implementation.castFunction_buffers _ _ (GuardedBranch.implementation_buffers _ _ _ _ _ _ core.roomTest_buffers
    (Implementation.then_buffers _ _ (Implementation.view_buffers _ _ _) (ListSnoc.buffers core.snocLayout))
    (Implementation.second_buffers (cost := .unit) (by decide) core.slotEntry core.slots core.wordFits core.appendInput_fits))).trans ?_
  omega

end Core

end Signatures.Runtime.CaliperBackend.SyncWrap
