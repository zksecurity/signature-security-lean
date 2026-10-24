import Proofs.Runtime.Caliper.InteractiveFoldPrepare

/-! A list fold with actual interactive body calls. The stored list length
controls early return; the capacity bounds the stored unrolling. The tail is
copied and retained across each body. Invariants reserve exactly the remaining
list length, even when the allocated list capacity is larger. -/
namespace Signatures.Runtime.CaliperBackend
open Caliper OracleComp OracleSpec

namespace Interactive
variable {w : Nat} {I B : Type} {spec : OracleSpec I}
theorem branch_at (port : Port w spec) (cost : WordIO.Costs) (tape : RandomTape w)
    (before : State w) (condition : Reg) (yes no : Code w) (output : Representation w B) (source : OracleComp spec B)
    (related : Synchronizes (Represents output cost tape ((if before.regs condition = 0 then no else yes).lower port) before)
      source ((if before.regs condition = 0 then no else yes).execute port cost tape before)) :
    Synchronizes (Represents output cost tape ((Code.branch condition yes no).lower port) before)
      source ((Code.branch condition yes no).execute port cost tape before) := by
  by_cases zero : before.regs condition = 0
  · rw [ite_eq_left zero] at related
    rw [Code.execute, ite_eq_left zero]
    simpa only [id_map] using related.map
      (result := Represents output cost tape ((Code.branch condition yes no).lower port) before) id
      (fun result => (fun finished => { finished with time := cost.machine.branch + finished.time }) <$> result) (by
        intro answer result related
        obtain ⟨finished, rfl, holds, remaining, execution⟩ := related
        exact ⟨{ finished with time := cost.machine.branch + finished.time }, rfl, holds, remaining, .branch_no zero execution⟩)
  · rw [ite_eq_right zero] at related
    rw [Code.execute, ite_eq_right zero]
    simpa only [id_map] using related.map
      (result := Represents output cost tape ((Code.branch condition yes no).lower port) before) id
      (fun result => (fun finished => { finished with time := cost.machine.branch + finished.time }) <$> result) (by
        intro answer result related
        obtain ⟨finished, rfl, holds, remaining, execution⟩ := related
        exact ⟨{ finished with time := cost.machine.branch + finished.time }, rfl, holds, remaining, .branch_yes zero execution⟩)
end Interactive

namespace InteractiveFold
variable {w : Nat} {A B I : Type} {spec : OracleSpec I}

def continuation (body following : Interactive.Code w) (buffer entry state capacity : Nat) : Interactive.Code w :=
  .seq (Interactive.retain body buffer (entry + state) state (1 + capacity * entry))
    (.seq (.compute (Assembly.code (Reorder.operands state (1 + capacity * entry) 0))) following)
def nonemptyCode (body following : Interactive.Code w) (buffer entry state capacity : Nat) : Interactive.Code w :=
  .seq (.compute (ListFold.prepare entry state 0 capacity)) (continuation body following buffer entry state capacity)
def code (body : Interactive.Code w) (buffer entry state : Nat) : Nat → Interactive.Code w
  | 0 => .compute (selectSlice 1 state)
  | capacity + 1 => .seq (.compute (.memLoad 1 0 0))
      (.branch 1 (nonemptyCode body (code body buffer entry state capacity) buffer entry state capacity)
        (.compute (selectSlice (1 + (capacity + 1) * entry) state)))
def denote (f : A × B → OracleComp spec B) {capacity : Nat} (value : BoundedList A capacity × B) : OracleComp spec B :=
  value.1.val.foldlM (fun accumulator head => f (head, accumulator)) value.2

variable (entry : Representation w A) (state : Representation w B) (hw : 16 < 2 ^ w)
    (argFits : entry.encoding.words + state.encoding.words < 2 ^ w)
    (port : Interactive.Port w spec) (invariant : Nat → B → Prop)
    {f : A × B → OracleComp spec B} {body : Interactive.Code w}
    (bodyRefines : ∀ remaining, Interactive.RefinesOn (fun value : A × B => invariant (remaining + 1) value.2)
      port .unit (entry.prod state argFits) state f body)
    (preserves : ∀ remaining value, invariant (remaining + 1) value.2 → ∀ answer ∈ support (f value), invariant remaining answer)

include hw bodyRefines in
theorem retained_refines (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.encoding.words + state.encoding.words < 2 ^ w) :
    Interactive.RefinesOn (fun value : (A × B) × BoundedList A capacity => invariant (value.2.val.length + 1) value.1.2)
      port .unit (preparedFrame entry state argFits capacity countFits storageFits)
      (state.prod (saved entry state capacity countFits storageFits) (by change _ + (1 + capacity * _) < _; nlinarith))
      (fun value => (fun answer => (answer, value.2)) <$> f value.1)
      (Interactive.retain body (Interactive.savedBuffer port body) (entry.encoding.words + state.encoding.words)
        state.encoding.words (1 + capacity * entry.encoding.words)) := by
  intro tape value valid before holds
  exact ((bodyRefines value.2.val.length).retain (by decide) (saved entry state capacity countFits storageFits) hw
    (preparedFrame entry state argFits capacity countFits storageFits).fits
    (by change _ + (1 + capacity * _) < _; nlinarith)) tape value valid before holds

include hw bodyRefines preserves in
theorem continuation_refines (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.encoding.words + state.encoding.words < 2 ^ w)
    {g : BoundedList A capacity × B → OracleComp spec B} {following : Interactive.Code w}
    (followingRefines : Interactive.RefinesOn (fun value : BoundedList A capacity × B => invariant value.1.val.length value.2)
      port .unit (frame entry state capacity (by omega) (by nlinarith)) state g following) :
    Interactive.RefinesOn (fun value : (A × B) × BoundedList A capacity => invariant (value.2.val.length + 1) value.1.2)
      port .unit (preparedFrame entry state argFits capacity countFits storageFits) state
      (fun value => f value.1 >>= fun answer => g (value.2, answer))
      (continuation body following (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity) := by
  let swap := Pairing.swap .unit (by decide) state (saved entry state capacity countFits storageFits) hw
    (by change _ + (1 + capacity * _) < _; nlinarith)
  have swapped := ((Interactive.Refines.compute port .unit swap).on
    (fun value : B × BoundedList A capacity => invariant value.2.val.length value.1)).seq followingRefines (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      exact valid)
  have composed := (retained_refines entry state hw argFits port invariant bodyRefines capacity countFits storageFits).seq swapped (by
    intro value valid answer reached
    rw [support_map, Set.mem_image] at reached
    obtain ⟨next, supported, rfl⟩ := reached
    exact preserves value.2.val.length value.1 valid next supported)
  convert composed using 1
  · funext value
    simp only [bind_map_left, pure_bind]
    rfl
  · rfl

include hw bodyRefines preserves in
theorem nonempty_refines (capacity : Nat) (countFits : capacity + 1 < 2 ^ w)
    (storageFits : 1 + (capacity + 1) * entry.encoding.words + state.encoding.words < 2 ^ w)
    {g : BoundedList A capacity × B → OracleComp spec B} {following : Interactive.Code w}
    (followingRefines : Interactive.RefinesOn (fun value : BoundedList A capacity × B => invariant value.1.val.length value.2)
      port .unit (frame entry state capacity (by omega) (by nlinarith)) state g following) :
    Interactive.RefinesOn (fun value : {value : BoundedList A (capacity + 1) × B // nonempty (capacity + 1) value} =>
      invariant value.val.1.val.length value.val.2) port .unit
      ((frame entry state (capacity + 1) countFits storageFits).restrict (nonempty (capacity + 1))) state
      (fun value => f (prepared value).1 >>= fun answer => g ((prepared value).2, answer))
      (nonemptyCode body following (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity) := by
  have composed := ((Interactive.Refines.compute port .unit (prepare entry state hw argFits capacity countFits storageFits)).on
    (fun value => invariant value.val.1.val.length value.val.2)).seq
    (continuation_refines entry state hw argFits port invariant bodyRefines preserves capacity countFits storageFits followingRefines) (by
      intro value valid answer reached
      simp only [support_pure, Set.mem_singleton_iff] at reached
      subst answer
      rcases value with ⟨⟨⟨values, bounded⟩, accumulator⟩, nonempty⟩
      cases values with
      | nil => exact False.elim (Nat.lt_irrefl 0 nonempty)
      | cons head tail => exact valid)
  convert composed using 1
  · funext value
    simp only [pure_bind]
  · rfl

include hw bodyRefines preserves in
theorem refines (capacity : Nat) (countFits : capacity < 2 ^ w)
    (storageFits : 1 + capacity * entry.encoding.words + state.encoding.words < 2 ^ w) :
    Interactive.RefinesOn (fun value : BoundedList A capacity × B => invariant value.1.val.length value.2)
      port .unit (frame entry state capacity countFits storageFits) state (denote f)
      (code body (Interactive.savedBuffer port body) entry.encoding.words state.encoding.words capacity) := by
  induction capacity with
  | zero =>
    intro tape value _ before holds
    have empty : value.1.val = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero value.1.property)
    have checked := (Interactive.Refines.compute port .unit (finish entry state hw 0 countFits storageFits)) tape value before holds
    simpa only [denote, empty, List.foldlM_nil, code, finish_code, Nat.zero_mul, Nat.add_zero] using checked
  | succ capacity ih =>
    intro tape value valid before holds
    rcases value with ⟨⟨values, bounded⟩, accumulator⟩
    have contents : (before.bufs 0).toList = BitVec.ofNat w values.length ::
      (entry.encoding.pack values ++ List.replicate ((capacity + 1 - values.length) * entry.encoding.words) 0) ++ state.encoding.encode accumulator := holds.2.1
    have loaded := Dispatch.load_tag .unit tape (BitVec.ofNat w values.length) _ before holds.1 contents
    apply Interactive.prepend_exec port .unit tape loaded
    apply Interactive.branch_at
    cases values with
    | nil =>
      rw [ite_eq_left (show (before.setReg 1 (BitVec.ofNat w ([] : List A).length)).regs 1 = 0 by simp)]
      have input : (frame entry state (capacity + 1) countFits storageFits).Holds (⟨[], bounded⟩, accumulator)
          (before.setReg 1 0) := ⟨by simpa using holds.1, holds.2.1, loaded.wellFormed_preserved holds.2.2.1, holds.2.2.2⟩
      exact (Interactive.Refines.compute port .unit (finish entry state hw (capacity + 1) countFits storageFits)) tape _ _ input
    | cons head tail =>
      have nonzero : BitVec.ofNat w (head :: tail).length ≠ 0 := by
        intro equal
        have natural := congrArg BitVec.toNat equal
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bounded.trans_lt countFits)] at natural
        simp at natural
      rw [ite_eq_right (by simpa using nonzero)]
      have following := ih (by omega) (by nlinarith)
      have checked := nonempty_refines entry state hw argFits port invariant bodyRefines preserves capacity countFits storageFits following
        tape ⟨(⟨head :: tail, bounded⟩, accumulator), by simp [nonempty]⟩ valid (before.setReg 1 (BitVec.ofNat w (head :: tail).length))
        ⟨by simpa using holds.1, holds.2.1, loaded.wellFormed_preserved holds.2.2.1, holds.2.2.2⟩
      simpa only [denote, List.foldlM_cons, prepared] using checked

end InteractiveFold
end Signatures.Runtime.CaliperBackend
