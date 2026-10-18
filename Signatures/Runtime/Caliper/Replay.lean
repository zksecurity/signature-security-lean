import Signatures.Runtime.Caliper.Memory

/-! A charged random-word recording/replay controller. Buffer 0 stores the
recorded prefix; register 0 is a virtual cursor and register 1 receives the next
word. Registers 2--4 are scratch. These are reserved controller locations; a
whole-program linker must keep attacker storage disjoint from them.

The physical tape cursor never rewinds. A replay reads ordinary stored words;
resetting the virtual cursor is an actual `imm` instruction. The cache's capacity
must be reserved and paid for before use.
-/

namespace Signatures.Runtime.CaliperBackend.Replay

open Caliper

variable {w : Nat}

def read : Stmt w :=
  .memLen 2 0 ;;
  .bin .ult 3 0 2 ;;
  .ifNZ 3 (.memLoad 1 0 0) (.rand 1 ;; .memPush 0 1) ;;
  .imm 4 1 ;;
  .bin .add 0 0 4

def rewind : Stmt w := .imm 0 0

theorem read_descriptionFits (hw : 16 < 2 ^ w) : DescriptionFits (read (w := w)) := by
  have hn : w ≠ 0 := by intro h; simp [h] at hw
  simp [DescriptionFits, read, description, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 1 < 2 ^ w by omega), hn]
  (repeat' constructor) <;>
    first | omega | (change 13 < 2 ^ w; omega) | (change 0 < 2 ^ w; positivity)

theorem read_descriptionWords : descriptionWords (read (w := w)) = 32 := rfl

/-- The controller is local to its reserved buffer and five registers. A
linker must establish this separation before placing it beside attacker code. -/
theorem read_frame {cost : CostModel} {tape : RandomTape w}
    {before after : State w} {elapsed : Nat} {net peak : Int}
    (execution : Caliper.Exec cost tape read before after elapsed net peak) :
    (∀ buffer, buffer ≠ 0 →
      after.bufs buffer = before.bufs buffer ∧ after.caps buffer = before.caps buffer) ∧
    (∀ register, 5 ≤ register → after.regs register = before.regs register) := by
  constructor
  · intro buffer distinct
    have untouched : ¬ (read (w := w)).Touches buffer := by simp [read, Stmt.Touches, distinct]
    exact ⟨execution.frame_buf untouched, execution.frame_cap untouched⟩
  · intro register reserved
    apply execution.frame_reg
    simp [read, Stmt.Writes]
    (repeat' constructor) <;> exact Nat.ne_of_gt (lt_of_lt_of_le (by decide) reserved)

def Ready (state : State w) : Prop :=
  (state.regs 0).toNat ≤ (state.bufs 0).size ∧
  (state.bufs 0).size ≤ state.caps 0 ∧ state.caps 0 < 2 ^ w ∧
  ((state.regs 0).toNat = (state.bufs 0).size → (state.bufs 0).size < state.caps 0)

def time (cost : CostModel) (fresh : Bool) : Nat :=
  cost.memLen + cost.bin .ult + cost.branch +
    (if fresh then cost.rand + cost.memPush else cost.memLoad) + cost.imm + cost.bin .add

private def prepare (before : State w) : State w :=
  (before.setReg 2 (BitVec.ofNat w (before.bufs 0).size)).setReg 3
    (if (before.regs 0).toNat < (before.bufs 0).size then 1 else 0)

private def finish (before : State w) : State w :=
  (before.setReg 4 1).setReg 0 (before.regs 0 + 1)

private theorem finish_exec (cost : CostModel) (tape : RandomTape w) (before : State w) :
    Caliper.Exec cost tape (.imm 4 1 ;; .bin .add 0 0 4) before (finish before)
      (cost.imm + cost.bin .add) 0 0 := by
  simpa [finish, BinOp.eval] using
    (Caliper.Exec.seq (Caliper.Exec.imm (C := cost) (tape := tape) (s := before) (d := 4) (v := 1))
      (Caliper.Exec.bin (op := .add) (d := 0) (a := 0) (b := 4)))

/-- Every successful read is either a cache load or a paid sample-and-store.
The postcondition exposes both virtual and physical cursor movement. -/
theorem read_exec (cost : CostModel) (tape : RandomTape w) (hw : 0 < w)
    (before : State w) (ready : Ready before) :
    ∃ after,
      Caliper.Exec cost tape read before after
        (time cost (decide ((before.regs 0).toNat = (before.bufs 0).size))) 0 0 ∧
      after.regs 1 = (if h : (before.regs 0).toNat < (before.bufs 0).size
        then (before.bufs 0)[(before.regs 0).toNat] else tape before.tapePos) ∧
      (after.regs 0).toNat = (before.regs 0).toNat + 1 ∧
      after.bufs 0 = (if (before.regs 0).toNat < (before.bufs 0).size
        then before.bufs 0 else (before.bufs 0).push (tape before.tapePos)) ∧
      after.tapePos = (if (before.regs 0).toNat < (before.bufs 0).size
        then before.tapePos else before.tapePos + 1) ∧
      after.caps = before.caps := by
  have hcursor := ready.1
  have hcapacity := ready.2.2.1
  have hlength : (before.bufs 0).size < 2 ^ w := ready.2.1.trans_lt ready.2.2.1
  have hnat : (BitVec.ofNat w (before.bufs 0).size).toNat = (before.bufs 0).size := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlength]
  have he₁ : Caliper.Exec cost tape (.memLen 2 0) before
      (before.setReg 2 (BitVec.ofNat w (before.bufs 0).size)) cost.memLen 0 0 := .memLen
  have he₂ : Caliper.Exec cost tape (.bin .ult 3 0 2)
      (before.setReg 2 (BitVec.ofNat w (before.bufs 0).size)) (prepare before) (cost.bin .ult) 0 0 := by
    convert Caliper.Exec.bin (C := cost) (tape := tape)
      (s := before.setReg 2 (BitVec.ofNat w (before.bufs 0).size)) (op := .ult)
      (d := 3) (a := 0) (b := 2) using 1
    simp [prepare, BinOp.eval, hnat]
  have hincrement : (before.regs 0 + (1 : Word w)).toNat = (before.regs 0).toNat + 1 := by
    have hbound : (before.regs 0).toNat + 1 < 2 ^ w := by
      by_cases h : (before.regs 0).toNat = (before.bufs 0).size
      · have := ready.2.2.2 h; omega
      · omega
    simp [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne'), Nat.mod_eq_of_lt hbound]
  by_cases cached : (before.regs 0).toNat < (before.bufs 0).size
  · let answered := (prepare before).setReg 1 (before.bufs 0)[(before.regs 0).toNat]
    have hload : ((prepare before).regs 0).toNat < ((prepare before).bufs 0).size := by
      simpa [prepare] using cached
    have he₃ : Caliper.Exec cost tape (.memLoad 1 0 0) (prepare before) answered cost.memLoad 0 0 := by
      convert Caliper.Exec.memLoad (C := cost) (tape := tape) hload using 1
      simp [answered, prepare]
    have hflag : (prepare before).regs 3 ≠ 0 := by simp [prepare, cached, hw.ne']
    have hb := Caliper.Exec.ifNZ_true (els := .rand 1 ;; .memPush 0 1) hflag he₃
    refine ⟨finish answered, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · have neq : ¬ (before.regs 0).toNat = (before.bufs 0).size := Nat.ne_of_lt cached
      simpa [read, time, neq, Nat.add_assoc] using
        Caliper.Exec.seq he₁ (Caliper.Exec.seq he₂ (Caliper.Exec.seq hb (finish_exec cost tape answered)))
    · simp [finish, answered, cached]
    · simpa [finish, answered, prepare] using hincrement
    · simp [finish, answered, prepare, cached]
    · simp [finish, answered, prepare, cached, State.setReg]
  · have equal : (before.regs 0).toNat = (before.bufs 0).size := by omega
    let sampled := (prepare before).readRandom tape 1
    let answered := sampled.setBuf 0 ((before.bufs 0).push (tape before.tapePos))
    have hpush : (sampled.bufs 0).size < sampled.caps 0 := by
      simpa [sampled, prepare] using ready.2.2.2 equal
    have hp : Caliper.Exec cost tape (.memPush 0 1) sampled answered cost.memPush 0 0 := by
      convert Caliper.Exec.memPush (C := cost) (tape := tape) (src := 1) hpush using 1
      simp [answered, sampled, prepare, State.readRandom, State.setReg]
    have hflag : (prepare before).regs 3 = 0 := by simp [prepare, cached]
    have hb := Caliper.Exec.ifNZ_false (thn := .memLoad 1 0 0) hflag
      (Caliper.Exec.seq (Caliper.Exec.rand (d := 1)) hp)
    refine ⟨finish answered, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simpa [read, time, equal, Nat.add_assoc] using
        Caliper.Exec.seq he₁ (Caliper.Exec.seq he₂ (Caliper.Exec.seq hb (finish_exec cost tape answered)))
    · simp [finish, answered, sampled, prepare, cached, State.readRandom, State.setReg, State.setBuf]
    · simpa [finish, answered, sampled, prepare, State.readRandom, State.setReg] using hincrement
    · simp [finish, answered, cached]
    · simp [finish, answered, sampled, prepare, cached, State.readRandom, State.setReg, State.setBuf]

/-- Reset only the stored virtual cursor, paying for the instruction. -/
theorem rewind_exec (cost : CostModel) (tape : RandomTape w) (before : State w) :
    Caliper.Exec cost tape rewind before (before.setReg 0 0) cost.imm 0 0 := .imm

/-- The buffer holds exactly the consumed prefix of a fixed external word tape.
The virtual cursor may be anywhere in that prefix after a rewind. -/
def Recorded (tape : RandomTape w) (state : State w) : Prop :=
  state.tapePos = (state.bufs 0).size ∧
  ∀ index (bound : index < (state.bufs 0).size), (state.bufs 0)[index] = tape index

theorem rewind_recorded (tape : RandomTape w) (before : State w) (recorded : Recorded tape before) :
    Recorded tape (before.setReg 0 0) := recorded

/-- Recording and replay return the same word as a virtual tape read. This proves
the semantic link, in addition to `read_exec`'s instruction/resource accounting. -/
theorem read_refines (cost : CostModel) (tape : RandomTape w) (hw : 0 < w)
    (before : State w) (ready : Ready before) (recorded : Recorded tape before) :
    ∃ after,
      Caliper.Exec cost tape read before after
        (time cost (decide ((before.regs 0).toNat = (before.bufs 0).size))) 0 0 ∧
      after.regs 1 = tape (before.regs 0).toNat ∧
      (after.regs 0).toNat = (before.regs 0).toNat + 1 ∧ Recorded tape after ∧
      after.caps = before.caps := by
  obtain ⟨after, execution, value, cursor, buffer, physical, capacities⟩ := read_exec cost tape hw before ready
  refine ⟨after, execution, ?_, cursor, ?_, capacities⟩
  · by_cases cached : (before.regs 0).toNat < (before.bufs 0).size
    · simpa [cached, recorded.2 _ cached] using value
    · have equal : (before.regs 0).toNat = (before.bufs 0).size := by have := ready.1; omega
      simpa [cached, recorded.1, equal] using value
  · constructor
    · rw [physical, buffer]
      split_ifs <;> simp [recorded.1]
    · intro index bound
      by_cases cached : (before.regs 0).toNat < (before.bufs 0).size
      · have hb : after.bufs 0 = before.bufs 0 := by simpa [cached] using buffer
        simpa only [hb] using recorded.2 index (by simpa only [hb] using bound)
      · have hb : after.bufs 0 = (before.bufs 0).push (tape before.tapePos) := by
          simpa [cached] using buffer
        by_cases old : index < (before.bufs 0).size
        · simpa [hb, Array.getElem_push, old] using recorded.2 index old
        · have hi : index = (before.bufs 0).size := by simp only [hb, Array.size_push] at bound; omega
          simp [hb, Array.getElem_push, hi, recorded.1]

theorem time_cached : time .unit false = 6 := rfl
theorem time_fresh : time .unit true = 7 := rfl

end Signatures.Runtime.CaliperBackend.Replay
