import Proofs.Runtime.Caliper.InteractiveFold

/-! Runtime bounds for effectful list traversal. The executed body is charged
on each nonempty row, together with copying the remaining tail and restoring
the next frame. Early return still charges its projection. -/
namespace Signatures.Runtime.CaliperBackend.InteractiveFold
open Caliper OracleComp OracleSpec
variable {w : Nat} {A B I : Type} {spec : OracleSpec I}

def width (entry state capacity : Nat) : Nat := 1 + (capacity + 1) * entry + state
def timeBudget (entry state capacity body : Nat) : Nat := 8 * state + capacity * (body + 44 * width entry state capacity + 7)

variable (entry : Representation w A) (state : Representation w B) (hw : 16 < 2 ^ w)
    (argFits : entry.encoding.words + state.encoding.words < 2 ^ w)
    (port : Interactive.Port w spec) (invariant : Nat → B → Prop)
    {f : A × B → OracleComp spec B} {body : Interactive.Code w}
    (bodyRefines : ∀ remaining, Interactive.RefinesOn (fun value : A × B => invariant (remaining + 1) value.2)
      port .unit (entry.prod state argFits) state f body)
    (preserves : ∀ remaining value, invariant (remaining + 1) value.2 → ∀ answer ∈ support (f value), invariant remaining answer)
    {bodyTime : Nat}
    (bodyBound : ∀ remaining, Interactive.TimeBoundOn (fun value : A × B => invariant (remaining + 1) value.2)
      port .unit (entry.prod state argFits) body bodyTime)

theorem finish_time (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words < 2 ^ w)
    (value : BoundedList A capacity × B) :
    (finish entry state hw capacity countFits storageFits).time value ≤ 8 * state.encoding.words := by
  change (selectSlice (w := w) (1 + capacity * entry.encoding.words) state.encoding.words).staticTime .unit ≤ _
  simp only [selectSlice_staticTime, sliceWordTime, CostModel.unit]
  omega

include hw bodyRefines bodyBound in
theorem retained_time (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.encoding.words + state.encoding.words < 2 ^ w) :
    Interactive.TimeBoundOn (fun value : (A × B) × BoundedList A capacity => invariant (value.2.val.length + 1) value.1.2)
      port .unit (preparedFrame entry state argFits capacity countFits storageFits)
      (Interactive.retain body (Interactive.savedBuffer port body) (entry.encoding.words + state.encoding.words)
        state.encoding.words (1 + capacity * entry.encoding.words))
      (bodyTime + 8 * (entry.encoding.words + state.encoding.words) + 8 * state.encoding.words + 12 * (1 + capacity * entry.encoding.words)) := by
  intro tape value valid before holds finished reached
  have bounded := Interactive.TimeBoundOn.retain (bodyRefines value.2.val.length) (bodyBound value.2.val.length)
    (by decide) (saved entry state capacity countFits storageFits) hw
    (preparedFrame entry state argFits capacity countFits storageFits).fits
  exact (bounded tape value valid before holds finished reached).trans (Interactive.retain_time_unit_le _ _ _ _ _)

include hw bodyRefines preserves bodyBound in
theorem continuation_time (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.encoding.words + state.encoding.words < 2 ^ w)
    {g : BoundedList A capacity × B → OracleComp spec B} {following : Interactive.Code w} {followingTime : Nat}
    (_followingRefines : Interactive.RefinesOn (fun value : BoundedList A capacity × B => invariant value.1.val.length value.2)
      port .unit (frame entry state capacity (by omega) (by nlinarith)) state g following)
    (followingBound : Interactive.TimeBoundOn (fun value : BoundedList A capacity × B => invariant value.1.val.length value.2)
      port .unit (frame entry state capacity (by omega) (by nlinarith)) following followingTime) :
    Interactive.TimeBoundOn (fun value : (A × B) × BoundedList A capacity => invariant (value.2.val.length + 1) value.1.2)
      port .unit (preparedFrame entry state argFits capacity countFits storageFits)
      (continuation body following (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity)
      (bodyTime + 8 * (entry.encoding.words + state.encoding.words) + 8 * state.encoding.words +
        12 * (1 + capacity * entry.encoding.words) + 8 * (state.encoding.words + (1 + capacity * entry.encoding.words)) + followingTime) := by
  let swap := Pairing.swap .unit (by decide) state (saved entry state capacity countFits storageFits) hw
    (by change _ + (1 + capacity * _) < _; nlinarith)
  have swapRefines := (Interactive.Refines.compute port .unit swap).on
    (fun value : B × BoundedList A capacity => invariant value.2.val.length value.1)
  have swapBound := (Interactive.TimeBound.compute (port := port) (cost := .unit) swap _
    (Pairing.swap_time_unit_le _ _ hw _)).on (fun value : B × BoundedList A capacity => invariant value.2.val.length value.1)
  have swapped := Interactive.TimeBoundOn.seq swapRefines swapBound followingBound (by
    intro value valid answer reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst answer
    exact valid)
  have bounded := Interactive.TimeBoundOn.seq
    (retained_refines entry state hw argFits port invariant bodyRefines capacity countFits storageFits)
    (retained_time entry state hw argFits port invariant bodyRefines bodyBound capacity countFits storageFits) swapped (by
      intro value valid answer reached
      rw [support_map, Set.mem_image] at reached
      obtain ⟨next, supported, rfl⟩ := reached
      exact preserves value.2.val.length value.1 valid next supported)
  apply bounded.mono
  dsimp only [saved, Representation.boundedList, Encoding.boundedList, Encoding.checked]
  omega

include hw bodyRefines preserves bodyBound in
theorem nonempty_time (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.encoding.words + state.encoding.words < 2 ^ w)
    {g : BoundedList A capacity × B → OracleComp spec B} {following : Interactive.Code w} {followingTime : Nat}
    (followingRefines : Interactive.RefinesOn (fun value : BoundedList A capacity × B => invariant value.1.val.length value.2)
      port .unit (frame entry state capacity (by omega) (by nlinarith)) state g following)
    (followingBound : Interactive.TimeBoundOn (fun value : BoundedList A capacity × B => invariant value.1.val.length value.2)
      port .unit (frame entry state capacity (by omega) (by nlinarith)) following followingTime) :
    Interactive.TimeBoundOn (fun value : {value : BoundedList A (capacity + 1) × B // nonempty (capacity + 1) value} =>
      invariant value.val.1.val.length value.val.2) port .unit
      ((frame entry state (capacity + 1) countFits storageFits).restrict (nonempty (capacity + 1)))
      (nonemptyCode body following (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity)
      (bodyTime + 44 * width entry.encoding.words state.encoding.words (capacity + 1) + 5 + followingTime) := by
  have prepared := (Interactive.Refines.compute port .unit (prepare entry state hw argFits capacity countFits storageFits)).on
    (fun value => invariant value.val.1.val.length value.val.2)
  have preparedBound := (Interactive.TimeBound.compute (port := port) (cost := .unit)
    (prepare entry state hw argFits capacity countFits storageFits) _
    (fun _ => ListFold.prepare_time_unit_le (w := w) entry.encoding.words state.encoding.words 0 capacity)).on
      (fun value => invariant value.val.1.val.length value.val.2)
  have bounded := Interactive.TimeBoundOn.seq prepared preparedBound
    (continuation_time entry state hw argFits port invariant bodyRefines preserves bodyBound capacity countFits storageFits followingRefines followingBound) (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      rcases value with ⟨⟨⟨values, bounded⟩, accumulator⟩, nonempty⟩
      cases values with
      | nil => exact False.elim (Nat.lt_irrefl 0 nonempty)
      | cons head tail => exact valid)
  apply bounded.mono
  dsimp only [ListFold.prepareWords, width]
  nlinarith

include hw bodyRefines preserves bodyBound in
theorem time_bound (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words < 2 ^ w) :
    Interactive.TimeBoundOn (fun value : BoundedList A capacity × B => invariant value.1.val.length value.2)
      port .unit (frame entry state capacity countFits storageFits)
      (code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity)
      (timeBudget entry.encoding.words state.encoding.words capacity bodyTime) := by
  induction capacity with
  | zero =>
    have bounded := (Interactive.TimeBound.compute (port := port) (cost := .unit) (finish entry state hw 0 countFits storageFits) _
      (finish_time entry state hw 0 countFits storageFits)).on (fun value => invariant value.1.val.length value.2)
    simpa only [code, finish_code, timeBudget, Nat.zero_mul, Nat.add_zero] using bounded
  | succ capacity ih =>
    intro tape value valid before holds finished reached
    rcases value with ⟨⟨values, listBound⟩, accumulator⟩
    have contents : (before.bufs 0).toList = BitVec.ofNat w values.length ::
      (entry.encoding.pack values ++ List.replicate ((capacity + 1 - values.length) * entry.encoding.words) 0) ++ state.encoding.encode accumulator := holds.2.1
    have loaded := Dispatch.load_tag .unit tape (BitVec.ofNat w values.length) _ before holds.1 contents
    let nextTime := timeBudget entry.encoding.words state.encoding.words capacity bodyTime
    let W := width entry.encoding.words state.encoding.words (capacity + 1)
    have bound := Interactive.time_prepend_at (port := port) tape loaded
      (Interactive.time_branch_at tape (before.setReg 1 (BitVec.ofNat w values.length)) 1 _ _
        (bodyTime + 44 * W + 5 + nextTime) (by
          cases values with
          | nil =>
            rw [ite_eq_left (show (before.setReg 1 (BitVec.ofNat w ([] : List A).length)).regs 1 = 0 by simp)]
            intro result supported
            have input : (frame entry state (capacity + 1) countFits storageFits).Holds (⟨[], listBound⟩, accumulator)
                (before.setReg 1 0) := ⟨by simpa using holds.1, holds.2.1, loaded.wellFormed_preserved holds.2.2.1, holds.2.2.2⟩
            have stopped := Interactive.TimeBound.compute (port := port) (cost := .unit)
              (finish entry state hw (capacity + 1) countFits storageFits) _ (finish_time entry state hw (capacity + 1) countFits storageFits)
            exact (stopped tape _ _ input result supported).trans (by dsimp [nextTime, timeBudget]; omega)
          | cons head tail =>
            have nonzero : BitVec.ofNat w (head :: tail).length ≠ 0 := by
              intro equal
              have natural := congrArg BitVec.toNat equal
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (listBound.trans_lt countFits)] at natural
              simp at natural
            rw [ite_eq_right (by simpa using nonzero)]
            have following := refines entry state hw argFits port invariant bodyRefines preserves capacity (by omega) (by nlinarith)
            have bounded := nonempty_time entry state hw argFits port invariant bodyRefines preserves bodyBound capacity countFits storageFits
              following (ih (by omega) (by nlinarith))
            exact bounded tape ⟨(⟨head :: tail, listBound⟩, accumulator), by simp [nonempty]⟩ valid _
              ⟨by simpa using holds.1, holds.2.1, loaded.wellFormed_preserved holds.2.2.1, holds.2.2.2⟩))
    apply (bound finished reached).trans
    have monotone : width entry.encoding.words state.encoding.words capacity ≤ W := by dsimp [width, W]; nlinarith
    have multiplied := Nat.mul_le_mul_left capacity (show bodyTime + 44 * width entry.encoding.words state.encoding.words capacity + 7 ≤ bodyTime + 44 * W + 7 by omega)
    change 1 + (1 + (bodyTime + 44 * W + 5 + nextTime)) ≤ _
    dsimp only [nextTime, timeBudget]
    change _ ≤ 8 * state.encoding.words + (capacity + 1) * (bodyTime + 44 * W + 7)
    rw [Nat.add_mul, Nat.one_mul]
    omega

end Signatures.Runtime.CaliperBackend.InteractiveFold
