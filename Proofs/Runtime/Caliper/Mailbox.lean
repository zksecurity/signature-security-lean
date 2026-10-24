import Proofs.Runtime.Caliper.Memory

/-! The local part of an oracle boundary: copy an encoded request to a mailbox,
or copy a resident reply into the caller's input buffer. The copy and allocation
execute in Caliper. Register 0 is restored to the local-call zero-offset ABI;
registers 1--4 are scratch. Private buffers and other registers are framed.

These routines do not implement the external oracle. A reply must already be
resident in a separately accounted input mailbox. In particular, this module
does not install an arbitrary host value into machine memory for free.
-/

namespace Signatures.Runtime.CaliperBackend.Mailbox

open Caliper

variable {w : Nat}

def transfer (source destination : BufId) : Stmt w :=
  copyBuffer source destination ;; .imm 0 0

def timeBound (cost : CostModel) (words : Nat) : Nat :=
  Corpus.Memcpy.timeBound cost words + cost.imm

theorem timeBound_unit (words : Nat) : timeBound .unit words = 7 * words + 5 := by
  rw [timeBound, copyBuffer_time]
  rfl

theorem transfer_randomFree (source destination : BufId) :
    (transfer (w := w) source destination).RandomFree := by
  simp [transfer, copyBuffer, Corpus.Memcpy.code, Stmt.RandomFree]

theorem transfer_descriptionFits (source destination : BufId)
    (hw : 16 < 2 ^ w) (hs : source < 2 ^ w) (hd : destination < 2 ^ w) :
    DescriptionFits (transfer (w := w) source destination) := by
  have hn : w ≠ 0 := by intro h; simp [h] at hw
  simp [DescriptionFits, transfer, copyBuffer, Corpus.Memcpy.code, description,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 1 < 2 ^ w by omega), hn]
  (repeat' constructor) <;>
    first | omega | (change 13 < 2 ^ w; omega) | (change 0 < 2 ^ w; positivity)

theorem transfer_descriptionWords (source destination : BufId) :
    descriptionWords (transfer (w := w) source destination) = 41 := by
  rfl

/-- A completed transfer preserves the private state outside its declared
destination and scratch registers, including capacities and the tape cursor. -/
theorem transfer_frame {cost : CostModel} {tape : RandomTape w}
    {source destination : BufId} {before after : State w} {elapsed : Nat} {net peak : Int}
    (execution : Caliper.Exec cost tape (transfer source destination) before after elapsed net peak) :
    (∀ buffer, buffer ≠ destination →
      after.bufs buffer = before.bufs buffer ∧ after.caps buffer = before.caps buffer) ∧
    (∀ register, 5 ≤ register → after.regs register = before.regs register) ∧
    after.tapePos = before.tapePos := by
  refine ⟨?_, ?_, execution.tapePos_eq_of_randomFree (transfer_randomFree _ _)⟩
  · intro buffer distinct
    have untouched : ¬ (transfer (w := w) source destination).Touches buffer := by
      simp [transfer, copyBuffer, Corpus.Memcpy.code, Stmt.Touches, distinct]
    exact ⟨execution.frame_buf untouched, execution.frame_cap untouched⟩
  · intro register reserved
    apply execution.frame_reg
    simp [transfer, copyBuffer, Corpus.Memcpy.code, Stmt.Writes]
    (repeat' constructor) <;> exact Nat.ne_of_gt (lt_of_lt_of_le (by decide) reserved)

/-- Allocation and every copied word are charged. The result is ready for a
local call at offset zero. Old destination capacity may be released, so the
memory claims are upper bounds on growth, not on total resident memory. -/
theorem transfer_spec (cost : CostModel) (tape : RandomTape w)
    (source destination : BufId) (distinct : destination ≠ source)
    (contents : Array (Word w)) (fits : contents.size < 2 ^ w) :
    Caliper.Triple cost tape (fun state => state.bufs source = contents)
      (transfer source destination)
      (fun state => state.bufs destination = contents ∧ state.bufs source = contents ∧ state.regs 0 = 0)
      (timeBound cost contents.size) contents.size contents.size := by
  intro before pre
  obtain ⟨middle, elapsed, net, peak, execution, result, ht, hn, hp⟩ :=
    copyBuffer_spec cost tape source destination distinct contents fits before pre
  refine ⟨middle.setReg 0 0, elapsed + cost.imm, net, max peak net, ?_, ?_, ?_, hn, ?_⟩
  · simpa [transfer] using Caliper.Exec.seq execution (Caliper.Exec.imm (d := 0) (v := 0))
  · exact ⟨result.1, result.2, by simp⟩
  · exact Nat.add_le_add_right ht _
  · exact max_le hp hn

end Signatures.Runtime.CaliperBackend.Mailbox
