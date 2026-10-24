import Proofs.Runtime.Caliper.Resources
import Caliper.Corpus.Memory

/-! Charged copying for snapshots. This reuses the verified Caliper memcpy loop,
including allocation time and peak destination storage. A full interactive
snapshot also needs saved registers, replay-buffer cursors and an ownership
discipline; copying one buffer does not by itself prove that protocol.
-/

namespace Signatures.Runtime.CaliperBackend

open Caliper

variable {w : Nat}

def copyBuffer (source destination : BufId) : Stmt w :=
  Corpus.Memcpy.code source destination

/-- The concrete loop is linear, not a constant-cost structural copy. -/
theorem copyBuffer_time (length : Nat) : Corpus.Memcpy.timeBound .unit length = 7 * length + 4 := by
  simp [Corpus.Memcpy.timeBound, CostModel.unit]
  omega

/-- Copying charges allocation and each transferred word. Bounds are upper
bounds, since an occupied destination first releases its previous capacity. -/
theorem copyBuffer_spec (cost : CostModel) (tape : RandomTape w)
    (source destination : BufId) (distinct : destination ≠ source)
    (contents : Array (Word w)) (fits : contents.size < 2 ^ w) :
    Caliper.Triple cost tape (fun state => state.bufs source = contents)
      (copyBuffer source destination)
      (fun state => state.bufs destination = contents ∧ state.bufs source = contents)
      (Corpus.Memcpy.timeBound cost contents.size) contents.size contents.size :=
  (Corpus.Memcpy.spec source destination distinct contents fits).withTape_of_randomFree
    (by simp [Corpus.Memcpy.code, Stmt.RandomFree]) tape

/-- This primitive does not alter the external random tape cursor. Tape replay
must use recorded words and an explicitly stored cursor; it is not a free reset. -/
theorem copyBuffer_tape {cost : CostModel} {tape : RandomTape w}
    {source destination : BufId} {before after : State w} {time : Nat} {net peak : Int}
    (execution : Caliper.Exec cost tape (copyBuffer source destination) before after time net peak) :
    after.tapePos = before.tapePos :=
  execution.tapePos_eq_of_randomFree (by simp [copyBuffer, Corpus.Memcpy.code, Stmt.RandomFree])

end Signatures.Runtime.CaliperBackend
