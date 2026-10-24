import Proofs.Runtime.Caliper.ListReverseBounds
import Proofs.Runtime.Caliper.BLSRecordLayout

/-! Charged chronological preparation of the BLS explicit-query transcript.
The original source view is implemented by actual list-reversal programs;
their copies, padding, retained context and stored bodies are all counted. -/

namespace Signatures.Runtime.CaliperBackend.BLSChronological
open Caliper BoundedSource

variable {w : Nat} {M G : Type} (layout : BLSRecord.Layouts w M G)

def reversal : ListReverse.Layouts w (M × G) where
  entry := layout.entry
  capacity := layout.capacityPred + 1
  wordFits := layout.wordFits
  countFits := layout.countFits
  storageFits := by
    apply layout.fits_of_le
    rw [BLSRecord.Layouts.entry_words]
    dsimp only [BLSRecord.Layouts.width, BLSRecord.Layouts.logWords]
    nlinarith

def hashes : Implementation .unit layout.transcript layout.log (fun tr => tr.1.reverse) :=
  (Implementation.first (by decide) layout.log layout.log layout.wordFits layout.transcript.representation.fits).then
    (ListReverse.implementation (reversal layout))

def signatures : Implementation .unit layout.transcript layout.log (fun tr => tr.2.reverse) :=
  (Implementation.second (by decide) layout.log layout.log layout.wordFits layout.transcript.representation.fits).then
    (ListReverse.implementation (reversal layout))

theorem hashes_buffers : (hashes layout).program.code.memBound ≤ 3 :=
  max_le ((Implementation.first_buffers _ _ _ _ _).trans (by decide)) (ListReverse.buffers (reversal layout))

theorem signatures_buffers : (signatures layout).program.code.memBound ≤ 3 :=
  max_le ((Implementation.second_buffers _ _ _ _ _).trans (by decide)) (ListReverse.buffers (reversal layout))

def implementation : Implementation .unit layout.transcript layout.transcript Signatures.Runtime.LazyAGM.chronological :=
  (hashes layout).pair (signatures layout) (by decide) layout.wordFits
    (layout.nameFits (hashes layout) (hashes_buffers layout) (by decide))
    (layout.nameFits (signatures layout) (signatures_buffers layout) (by decide))
    (layout.fits_of_le (by rw [BLSRecord.Layouts.transcript_words]; dsimp only [BLSRecord.Layouts.width]; omega))
    (layout.fits_of_le (by rw [BLSRecord.Layouts.log_words, BLSRecord.Layouts.transcript_words]; dsimp only [BLSRecord.Layouts.width]; omega))
    layout.transcript.representation.fits

def timeBudget : Nat := 2 * ListReverse.timeBudget (reversal layout) + 172 * layout.logWords
def codeBudget : Nat := 2 * ListReverse.codeBudget (reversal layout) + 559 * layout.logWords + 154

theorem hashes_bounded : (hashes layout).BoundedBy
    (8 * layout.logWords + ListReverse.timeBudget (reversal layout))
    (26 * layout.logWords + 14 + ListReverse.codeBudget (reversal layout) + 1) :=
  (Implementation.first_boundedBy layout.log layout.log layout.wordFits layout.transcript.representation.fits).then
    (ListReverse.bounded (reversal layout))

theorem signatures_bounded : (signatures layout).BoundedBy
    (8 * layout.logWords + ListReverse.timeBudget (reversal layout))
    (26 * layout.logWords + 14 + ListReverse.codeBudget (reversal layout) + 1) :=
  (Implementation.second_boundedBy layout.log layout.log layout.wordFits layout.transcript.representation.fits).then
    (ListReverse.bounded (reversal layout))

theorem bounded : (implementation layout).BoundedBy (timeBudget layout) (codeBudget layout) := by
  apply (Implementation.pair_boundedBy _ _ _ _ _ _ _ _ (hashes_bounded layout) (signatures_bounded layout)).mono
  all_goals simp only [BLSRecord.Layouts.transcript_words, BLSRecord.Layouts.log_words, timeBudget, codeBudget]; omega

theorem buffers : (implementation layout).program.code.memBound ≤ 4 :=
  Implementation.pair_buffers (firstBuffers := 3) (secondBuffers := 3) _ _ _ _ _ _ _ _
    (hashes_buffers layout) (signatures_buffers layout)

theorem names (slots : Nat) : NamesAccounted (implementation layout).program.code slots :=
  Implementation.pair_names _ _ _ _ _ _ _ _
    ((Implementation.first_names layout.log layout.log layout.wordFits layout.transcript.representation.fits slots).seq
      (ListReverse.names (reversal layout) slots))
    ((Implementation.second_names layout.log layout.log layout.wordFits layout.transcript.representation.fits slots).seq
      (ListReverse.names (reversal layout) slots))

theorem resources (tape : RandomTape w) (value : layout.transcript.Value) (before : State w)
    (holds : layout.transcript.representation.Holds value before) (registers buffers : Nat)
    (initialRegisters : RegisterBound before registers) (initialBuffers : before.SupportBound buffers) :
    ∃ after net peak, Caliper.Exec .unit tape (implementation layout).program.code before after
      ((implementation layout).program.time value) net peak ∧
      layout.transcript.representation.Holds
        ⟨Signatures.Runtime.LazyAGM.chronological value.val, (implementation layout).preserves value.val value.property⟩ after ∧
      (implementation layout).program.time value ≤ timeBudget layout ∧
      ∀ between, (Caliper.Reaches .unit tape (implementation layout).program.code before between ∨ between = after) →
        (staticWords (implementation layout).program.code registers buffers : Int) +
          between.liveMem (max buffers (implementation layout).program.code.memBound) ≤
          5 * codeBudget layout + registers + 3 * buffers + before.liveMem buffers + timeBudget layout := by
  obtain ⟨after, net, peak, execution, output, elapsed, _, peakBound⟩ := (bounded layout).exec (by decide) tape value before holds
  refine ⟨after, net, peak, execution, output, elapsed, ?_⟩
  intro between visited
  have memory := (LocalReach.total_memory_bound execution visited registers buffers initialRegisters initialBuffers holds.2.2.1).2.2.2
  have stored := (bounded layout).code_le
  have registerBound := (names layout 0).registers
  have bufferBound := (names layout 0).buffers
  have staticBound : staticWords (implementation layout).program.code registers buffers ≤
      5 * codeBudget layout + registers + 3 * buffers := by unfold staticWords; omega
  omega

end Signatures.Runtime.CaliperBackend.BLSChronological
